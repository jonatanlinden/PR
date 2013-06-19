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

#include <stdio.h>
#include <stdlib.h>

#include <errno.h>

#include <signal.h>

#include <sys/time.h>

#include <sys/times.h>

#include <unistd.h>
#include <limits.h>
#include <assert.h>
#include <stdarg.h>
#include <math.h>

#include <sched.h>
#include <sys/syscall.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>

#include "portable_defns.h"
#include "prioq.h"
#include "ptst.h"
#include "j_util.h"



#define MAX_ITERATIONS 100000000
#define MAX_WALL_TIME 10 /* seconds */

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

/*    fprintf (stdout, "-------------------------------------------"
             "---------------------------\n");

    for (i = 0; i < num_log_records; i ++)
    {

        fprintf (stdout, "%s\t = ", log_records[i].name);
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
*/
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


unsigned long long max_key;

static bool_t go = FALSE;
static int threads_initialised1 = 0, log_max_key;
static int threads_initialised2 = 0, max_offset;
static int threads_initialised3 = 0;
int num_threads;

static unsigned long arrival_intensity;
static unsigned long local_comp;

static struct timeval start_time, done_time;
static struct tms start_tms, done_tms;

static int delete_successes[MAX_THREADS];
static int update_successes[MAX_THREADS];
static uint64_t global_sleeptime = 0;


/* All the variables accessed in the critical main loop. */
static struct {
    CACHE_PAD(0);
    bool_t alarm_time;
    CACHE_PAD(1);
    set_t *set;
    CACHE_PAD(2);
} shared;

void
gen_lfsr(unsigned long*arr, int len)
{
    unsigned long lfsr = 1;
    unsigned period = 0;
    do
    {
        /*taps: 32 31 29 1; feedback polynomial: x^32 + x^31 + x^29 + x + 1*/
        lfsr = (lfsr >> 1) ^ (-(lfsr & 1u) & 0xD0000001u); 
	arr[period] = (unsigned long) lfsr;
        ++period;
    } while(lfsr != 1u && period < len);

}

void
gen_exps(unsigned long *arr, int len, int intens)
{
    int i = 0;
    arr[0] = 2;
    while (i + 1 < len) {
       arr[i+1] = arr[i] + 1 + (unsigned long)ceil(gsl_ran_exponential (rng[0], intens));
       i++;
    }
}
static unsigned long *exps;
static int exps_pos = 0;

static void alarm_handler( int arg)
{
    shared.alarm_time = 1;
}


static void *thread_start(void *arg)
{
    //unsigned long k, ok;
    setkey_t k, ok;
    int i, j;
    void *ov, *v;
    long id = (long)arg;

    unsigned long r = ((unsigned long)arg)+3; /*RDTICK();*/
    unsigned int intens = arrival_intensity;
    unsigned int local = local_comp;

    v = (void *)8888888888;

#define PIN
#ifdef PIN
    //pin (gettid(), 4*(unsigned long)arg);
    // straight allocation
    pin (gettid(), id/8 + 4*(id % 8));
#endif
    
    rng[id] = gsl_rng_alloc(gsl_rng_mt19937);
    gsl_rng_set(rng[id], time(NULL)+id);
    
#define EXPS 90000000
    if ( id == 0 )
    {
        _init_gc_subsystem();
        _init_set_subsystem();
        shared.set = set_alloc(max_offset, 20, num_threads);
	exps = (unsigned long *)malloc(sizeof(unsigned long) * EXPS);
	gen_exps(exps, EXPS, 1000);
	//gen_lfsr(exps, EXPS);
	

	for (i = 0; i < max_key; i++) {
	    set_update(shared.set, exps[exps_pos], v);
	    exps_pos++;
	    }

	/*for (i = 1; i <= max_key; i++) {
	    set_update(shared.set, i, v);
	    }*/
	//sequential_length(shared.set);
    }

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
    uint64_t local_sum  = 0;
    int kcnts = 0;
    
    for ( i = 0; (i < MAX_ITERATIONS) && !shared.alarm_time; i++ )
    {

	/***********************************************
	 * Deterministic execution.
	 */

	v = (void *)99999999999;

	// always increase.
	k = set_removemin(shared.set);
	
	assert(k != ok);
	
	local_sum+=k;
	ok = k;
	
	del_cnt++;

	//k = k + max_key;

	j = __sync_fetch_and_add(&exps_pos, 1);
	
	set_update(shared.set, exps[j], v);
	
	// local work...
	volatile int kk = 0;
	for (j = 0; j < local; j++) {
	    kk = j;
	    __asm__("");
	}
    }

    // checksum calculation
    //printf("local_sum: %llu\n", local_sum);

    /* BARRIER FOR ALL THREADS */
    {
        int n_id, id = threads_initialised3;
        while ( (n_id = CASIO(&threads_initialised3, id, id+1)) != id ) 
            id = n_id;
    }
    while ( threads_initialised3 != num_threads ) MB();
    
    //printf("kcnts: %d\n", kcnts);
    


    if ( id == num_threads - 1 )
    {
        gettimeofday(&done_time, NULL);
        times(&done_tms);
        WMB();
	//sequential_length(shared.set);
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
    int fd;
    pthread_t            thrs[MAX_THREADS];
    int num_successes;
    int num_upd_successes;
    int min_successes, max_successes;
    int ticksps = sysconf(_SC_CLK_TCK);
    float wall_time, user_time, sys_time;

    if ( num_threads == 1 ) goto skip_thread_creation;

#ifdef PIN
    pin(gettid(), 0);
#endif

    for (long i = 0; i < num_threads; i ++)
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
        for (int i = 0; i < num_threads; i ++)
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
    for (int i = 0; i < num_threads; i++ )
    {
        num_successes += delete_successes[i];
	num_upd_successes += update_successes[i];
	
        if ( delete_successes[i] < min_successes ) min_successes = delete_successes[i];
        if ( delete_successes[i] > max_successes ) max_successes = delete_successes[i];
    }

    log_int ("min_succ", min_successes);
    log_int ("max_succ", max_successes);
    log_int ("num_del_succ", num_successes);
    log_int ("num_upd_succ", num_upd_successes);
    log_float("us_per_succ", (num_threads*wall_time*1000000.0)/num_successes);

    log_int("log max key", log_max_key);
    printf("avg sleeptime: %llu\n", global_sleeptime/32);
}

int main (int argc, char **argv)
{

    if ( argc != 6 )
    {
        printf("%s <num_threads> <arrival_intens> <key power> <max_offset> <local_comp>\n"
               , argv[0]);
        exit(1);
    }

    memset(&shared, 0, sizeof(shared));

    num_threads = atoi(argv[1]);
    log_int ("num_threads", num_threads);


    arrival_intensity = atoi(argv[2]);
    log_int("arrival_intens", arrival_intensity);
    
    log_max_key = atoi(argv[3]);
    max_key = 1ULL << atoi(argv[3]);
    log_int("num_elements", max_key);

    max_offset = atoi(argv[4]);
    log_int("max_offset", max_offset);

    local_comp = atoi(argv[5]);
    log_int("local_comp", local_comp);


    log_int ("max_iterations", MAX_ITERATIONS);
    log_int ("wall_time_lim_s", MAX_WALL_TIME);


    test_multithreaded ();
    
    dump_log ();
    exit(0);
}

