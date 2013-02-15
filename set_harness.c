/******************************************************************************
 * set_harness.c
 * 
 * Test harness for the various set implementations.
 * 
 * Copyright (c) 2002-2003, K A Fraser
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright 
 * notice, this list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright 
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * 
 * * The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR 
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED 
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE 
 * DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, 
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES 
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR 
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) 
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, 
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN 
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
 * POSSIBILITY OF SUCH DAMAGE.
 */

#define _GNU_SOURCE

#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
//#include <ucontext.h>
#include <signal.h>
#include <sched.h>
#include <limits.h>
#include <assert.h>
#include <stdarg.h>
#include <math.h>

#include <sched.h>
#include <sys/syscall.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>



#include "portable_defns.h"
#include "set.h"
#include "ptst.h"
#include "j_util.h"


/* This produces an operation log for the 'replay' checker. */
//#define DO_WRITE_LOG

#ifdef DO_WRITE_LOG
#define MAX_ITERATIONS 100000
#define MAX_WALL_TIME 50 /* seconds */
#else
#define MAX_ITERATIONS 100000000
#define MAX_WALL_TIME 10 /* seconds */
#endif

pid_t 
gettid(void) 
{
    return (pid_t) syscall(SYS_gettid);
}


void
pin(pid_t t, int cpu) 
{
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(cpu, &cpuset);
    sched_setaffinity(t, sizeof(cpu_set_t), &cpuset);
}


gsl_rng *rng[64];



/*
 * ***************** LOGGING
 */

#define MAX_LOG_RECORDS 256

#define LOG_KIND_INT 0
#define LOG_KIND_STRING 1
#define LOG_KIND_FLOAT 2

typedef struct {
    char *name;
    int kind;
    long val_int;
    char *val_string;
    float val_float;
} log_record_t;

static log_record_t log_records[MAX_LOG_RECORDS];

static int num_log_records = 0;

static void log_int (char *name, long val) {
    log_records[num_log_records].name = name;
    log_records[num_log_records].kind = LOG_KIND_INT;
    log_records[num_log_records].val_int = val;
    num_log_records ++;
}

static void log_string (char *name, char *val) {
    log_records[num_log_records].name = name;
    log_records[num_log_records].kind = LOG_KIND_STRING;
    log_records[num_log_records].val_string = val;
    num_log_records ++;
}

static void log_float (char *name, float val) {
    log_records[num_log_records].name = name;
    log_records[num_log_records].kind = LOG_KIND_FLOAT;
    log_records[num_log_records].val_float = val;
    num_log_records ++;
}

static void dump_log (void) {
    int i;

    fprintf (stdout, "-------------------------------------------"
             "---------------------------\n");
    for (i = 0; i < num_log_records; i ++)
    {
        char padding[40];
        strcpy(padding, "                                        ");
        if (30-strlen(log_records[i].name) >= 0){
            padding[30-strlen(log_records[i].name)] = '\0';
        }
        fprintf (stdout, "%s%s = ", padding, log_records[i].name);
        {
            int kind = log_records [i].kind;
            if (kind == LOG_KIND_INT) {
                fprintf (stdout, "%d\n", log_records[i].val_int);
            } else if (kind == LOG_KIND_STRING) {
                fprintf (stdout, "%s\n", log_records[i].val_string);
            } else if (kind == LOG_KIND_FLOAT) {
                fprintf (stdout, "%.3f\n", log_records[i].val_float);
            } 
        }
    }
    fprintf (stdout, "-------------------------------------------"
             "---------------------------\n");

    for (i = 0; i < num_log_records; i ++)
    {
        int kind = log_records [i].kind;
        if (i != 0) { fprintf (stderr, " "); }
        if (kind == LOG_KIND_INT) {
            fprintf (stderr, "%d", log_records[i].val_int);
        } else if (kind == LOG_KIND_STRING) {
            fprintf (stderr, "%s", log_records[i].val_string);
        } else if (kind == LOG_KIND_FLOAT) {
            fprintf (stderr, "%.3f", log_records[i].val_float);
        } 
    }
    fprintf (stderr, " LOG\n");
}

/*
 * ************** END OF LOGGING
 */

#define TVAL(x) ((x.tv_sec * 1000000) + x.tv_usec)

/* Log tables. Written out at end-of-day. */
typedef struct log_st
{
    interval_t    start, end;
    unsigned int  key;
    void         *val, *old_val; /* @old_val used by update() and remove() */
} log_t;
#define SIZEOF_GLOBAL_LOG (num_threads*MAX_ITERATIONS*sizeof(log_t))
static log_t *global_log;
static interval_t interval = 0;

unsigned long long max_key;

static bool_t go = FALSE;
static int threads_initialised1 = 0, log_max_key;
static int threads_initialised2 = 0, max_offset;
static int threads_initialised3 = 0;
int num_threads;

static unsigned long proportion;
static unsigned long arrival_intensity;
static unsigned long local_comp;



static struct timeval start_time, done_time;
static struct tms start_tms, done_tms;

static int delete_successes[MAX_THREADS];
static int update_successes[MAX_THREADS];


/* All the variables accessed in the critical main loop. */
static struct {
    CACHE_PAD(0);
    bool_t alarm_time;
    CACHE_PAD(1);
    set_t *set;
    CACHE_PAD(2);
} shared;

#define nrand(_r) (((_r) = (_r) * 1103515245) + 12345)

static void alarm_handler( int arg)
{
    shared.alarm_time = 1;
}


static void *thread_start(void *arg)
{
    unsigned long k, ok;
    int i;
    void *ov, *v;
    int id = (int)arg;
#ifdef DO_WRITE_LOG
    log_t *log = global_log + id*MAX_ITERATIONS;
    interval_t my_int;
#endif
    unsigned long r = ((unsigned long)arg)+3; /*RDTICK();*/
    unsigned int intens = arrival_intensity;
    unsigned int local = local_comp;

    pin (gettid(), (unsigned long)arg);

    rng[id] = gsl_rng_alloc(gsl_rng_mt19937);
    gsl_rng_set(rng[id], time(NULL)+id);
    

    if ( id == 0 )
    {
        _init_ptst_subsystem();
        _init_gc_subsystem();
        _init_set_subsystem();
        shared.set = set_alloc(max_offset);
    }

    /* BARRIER FOR ALL THREADS */
    {
        int n_id, id = threads_initialised1;
        while ( (n_id = CASIO(&threads_initialised1, id, id+1)) != id )
            id = n_id;
    }
    while ( threads_initialised1 != num_threads ) MB();

#ifndef DO_WRITE_LOG
    /* Start search structure off with a well-distributed set of inital keys */

    if (id == 0) {
    for (i = 1; i < max_key; i++) {
	set_update(shared.set, i, (void *)i+1, 1, id);//(void *)0xdeadbee0, 1);
    }
    printf("init ready\n");
    printf("num elements: %llu\n", max_key);
    
    }

#endif

    {
        int n_id, id = threads_initialised2;
        while ( (n_id = CASIO(&threads_initialised2, id, id+1)) != id )
            id = n_id;
    }
    while ( threads_initialised2 != num_threads ) MB();

    if ( id == 0 )
    {
        (void)signal(SIGALRM, &alarm_handler);
        (void)alarm(MAX_WALL_TIME);
        WMB();
        gettimeofday(&start_time, NULL);
        times(&start_tms);
        go = TRUE;
        WMB();
    } 
    else 
    {
        while ( !go ) MB();
    }
    int del_cnt = 0;
    int upd_cnt = 0;
    ov = NULL;
    ok = 0;
    
#ifdef DO_WRITE_LOG
    get_interval(my_int);
#endif
    uint64_t now;
    

    for ( i = 0; (i < MAX_ITERATIONS) && !shared.alarm_time; i++ )
    {
	//k = (nrand(r) >> 4) & (_max_key - 1);
	
        nrand(r);
#ifdef DO_WRITE_LOG
        log->start = my_int;
#endif


#define DETERM

	/***********************************************
	 * Deterministic execution.
	 */
#ifdef DETERM
	v = (void *)((r&~7)|0x8);
	
	// always increase.

	k = set_removemin(shared.set, id);
	//printf("K: %lu\n", k);
	
	//if (k > 1) { // success
	del_cnt++;
	ok = k;
//	}
        //k = ok + 1 + gsl_ran_geometric (rng[id], intens);
	k = ok + 1 + (long)ceil(gsl_ran_exponential (rng[id], intens));
	ov = set_update(shared.set, k, v, 1, id);
	//upd_cnt++; 
    
	now = read_tsc_p();
	//sleep
	while(read_tsc_p() - now < local)
	    ;
	
#else
	//if ( ((r>>4)&255) < prop )
	//{
	//ov = v = set_lookup(shared.set, k);
	//}
	
	if ( ((r>>12)&1) )
	{
            v = (void *)((r&~7)|0x8);
	    // always increase... (geometric dist.)
	    k = (long)ceil(gsl_ran_exponential (rng[id], intens));
	    k = ok + k;
	    //k = ok + gsl_ran_geometric (rng[id], 0.001);
	
	    //if (!(i % 1000000)) {
	    //printf("new k: %llu\n", k);
	    //}

            ov = set_update(shared.set, k, v, 1, id);
	    upd_cnt++;
	} else {
            k = set_removemin(shared.set);

	    v = NULL;
	    if (k > 1) {
		del_cnt++;
		ok = k;
	    }
        }

#endif

#ifdef DO_WRITE_LOG
        get_interval(my_int);
        log->key = k;
        log->val = v;
        log->old_val = ov;
        log->end = my_int;
        log++;
#endif
    }

    /* BARRIER FOR ALL THREADS */
    {
        int n_id, id = threads_initialised3;
        while ( (n_id = CASIO(&threads_initialised3, id, id+1)) != id ) 
            id = n_id;
    }
    while ( threads_initialised3 != num_threads ) MB();

#if 0
    if ( id == 0 )
    {
        extern void check_tree(set_t *);
        check_tree(shared.set);
    }
#endif

    if ( id == num_threads - 1 )
    {
        gettimeofday(&done_time, NULL);
        times(&done_tms);
        WMB();
        _destroy_gc_subsystem();
    } 

    delete_successes[id] = del_cnt;
    update_successes[id] = upd_cnt;
    
    return(NULL);
}

#define THREAD_TEST thread_start
#define THREAD_FLAGS THR_BOUND

static void test_multithreaded (void)
{
    int                 i, fd;
    pthread_t            thrs[MAX_THREADS];
    int num_successes;
    int num_upd_successes;
    int min_successes, max_successes;
    int ticksps = sysconf(_SC_CLK_TCK);
    float wall_time, user_time, sys_time;

    if ( num_threads == 1 ) goto skip_thread_creation;

    pthread_setconcurrency(num_threads);
    

    for (i = 0; i < num_threads; i ++)
    {
        MB();
        pthread_create (&thrs[i], NULL, THREAD_TEST, (void *)i);
    }

 skip_thread_creation:
    if ( num_threads == 1 )
    {
	MB();
	
        thread_start(0);
    }
    else
    {
        for (i = 0; i < num_threads; i ++)
        {
            (void)pthread_join (thrs[i], NULL);
        }
    }

    wall_time = (float)(TVAL(done_time) - TVAL(start_time))/ 1000000;
    user_time = ((float)(done_tms.tms_utime - start_tms.tms_utime))/ticksps;
    sys_time  = ((float)(done_tms.tms_stime - start_tms.tms_stime))/ticksps;

    log_float ("wall_time_s", wall_time);
    log_float ("user_time_s", user_time);
    log_float ("system_time_s", sys_time);

    num_successes = 0;
    num_upd_successes = 0;
    
    min_successes = INT_MAX;
    max_successes = INT_MIN;
    for ( i = 0; i < num_threads; i++ )
    {
        num_successes += delete_successes[i];
	num_upd_successes += update_successes[i];
	//printf("tid %d: del successes: %d\n", i,delete_successes[i]);
	//printf("tid %d: upd successes: %d\n", i,update_successes[i]);
	
	
        if ( delete_successes[i] < min_successes ) min_successes = delete_successes[i];
        if ( delete_successes[i] > max_successes ) max_successes = delete_successes[i];
    }

    log_int ("min_successes", min_successes);
    log_int ("max_successes", max_successes);
    log_int ("num_del_successes", num_successes);
    log_int ("num_upd_successes", num_upd_successes);
    log_float("us_per_success", (num_threads*wall_time*1000000.0)/num_successes);

    log_int("log max key", log_max_key);
}

#if defined(INTEL)
static void tstp_handler(int sig, siginfo_t *info, ucontext_t *uc)
{
    static unsigned int sem = 0;
    unsigned long *esp = (unsigned long *)(uc->uc_mcontext.gregs[7]);
    int pid = getpid();

    while ( CASIO(&sem, 0, 1) != 0 ) sched_yield();

    printf("Signal %d for pid %d\n", sig, pid);
    printf("%d: EIP=%08x  EAX=%08x  EBX=%08x  ECX=%08x  EDX=%08x\n", pid,
           uc->uc_mcontext.gregs[14], uc->uc_mcontext.gregs[11],
           uc->uc_mcontext.gregs[ 8], uc->uc_mcontext.gregs[10],
           uc->uc_mcontext.gregs[ 9]);
    printf("%d: ESP=%08x  EBP=%08x  ESI=%08x  EDI=%08x  EFL=%08x\n", pid,
           uc->uc_mcontext.gregs[ 7], uc->uc_mcontext.gregs[ 6],
           uc->uc_mcontext.gregs[ 5], uc->uc_mcontext.gregs[ 4],
           uc->uc_mcontext.gregs[16]);
    printf("\n");

    sem = 0;

    for ( ; ; ) sched_yield();
}
#endif

int main (int argc, char **argv)
{
#ifdef DO_WRITE_LOG
    int fd;
    unsigned long log_header[] = { 0, MAX_ITERATIONS, 0 };

    if ( argc != 7 )
    {
        printf("%s <num_threads> <arrival_intens> <key power> <log name>\n"
               , argv[0]);
        exit(1);
    }
#else
    if ( argc != 6 )
    {
        printf("%s <num_threads> <arrival_intens> <key power> <max_offset> <local_comp>\n"
               , argv[0]);
        exit(1);
    }
#endif

    memset(&shared, 0, sizeof(shared));

    num_threads = atoi(argv[1]);
    log_int ("num_threads", num_threads);

    proportion = 0;

    arrival_intensity = atoi(argv[2]);
    log_int("arrival_intensity", arrival_intensity);
    
    log_max_key = atoi(argv[3]);
    max_key = 1ULL << atoi(argv[3]);
    log_int("num_elements", max_key);

    max_offset = atoi(argv[4]);
    log_int("max_offset", max_offset);

    local_comp = atoi(argv[5]);
    log_int("local_comp", local_comp);


    log_int ("max_iterations", MAX_ITERATIONS);
    log_int ("wall_time_limit_s", MAX_WALL_TIME);

#ifdef DO_WRITE_LOG
    log_header[0] = num_threads;
    log_header[2] = max_key;
    global_log = malloc(SIZEOF_GLOBAL_LOG);
#endif

/* #if defined(INTEL) */
/*     { */
/*         struct sigaction act; */
/*         memset(&act, 0, sizeof(act)); */
/*         act.sa_handler = (void *)tstp_handler; */
/*         act.sa_flags = SA_SIGINFO; */
/*         sigaction(SIGTSTP, &act, NULL); */
/*         sigaction(SIGQUIT, &act, NULL); */
/*         sigaction(SIGSEGV, &act, NULL); */
/*     } */
/* #endif */

    test_multithreaded ();

    dump_log ();

#ifdef DO_WRITE_LOG
    printf("Writing log...\n");
    /* Write logs to data file */
    fd = open(argv[5], O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if ( fd == -1 )
    {
        fprintf(stderr, "Error writing log!\n");
        exit(-1);
    }

    if ( (write(fd, log_header, sizeof(log_header)) != sizeof(log_header)) ||
         (write(fd, global_log, SIZEOF_GLOBAL_LOG) != SIZEOF_GLOBAL_LOG) )
    {
        fprintf(stderr, "Log write truncated or erroneous\n");
        close(fd);
        exit(-1);
    }

    close(fd);
#endif

    exit(0);
}

