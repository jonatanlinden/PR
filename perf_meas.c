/** 
 * Priority queue test harness.
 *
 * Author: Jonatan Linden <jonatan.linden@it.uu.se>
 *
 * Time-stamp: <2013-10-28 13:40:02 jonatanlinden>
 */

#define _GNU_SOURCE
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <pthread.h>
#include <sys/time.h>
#include <assert.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include <sched.h>
#include <sys/syscall.h>

#include "common.h"
#include "prioq.h"
#include "gc.h"



#define DEFAULT_GCYCLES 10
#define DEFAULT_NTHREADS 1
#define DEFAULT_OFFSET 64


#define PIN

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
    E_en(sched_setaffinity(t, sizeof(cpu_set_t), &cpuset));
}



void *run (void *_args);

pthread_t *ts;

pq_t *pq;

volatile int start = 0;


/* global timestamp deciding when all threads should stop */
uint64_t end = 0;
/* global total measure */
unsigned long measure = 0;


#define NOW() read_tsc_p()

static void
usage(FILE *out, const char *argv0)
{
    fprintf(out, "Usage: %s [OPTION]...\n"
                        "\n"
	    "Options:\n", argv0);

    fprintf(out, "\t-h\t\tDisplay usage.\n");
    fprintf(out, "\t-t GCYCLES\tRun for GCYCLES billion cycles. "
	    "Default: %i\n",
	    DEFAULT_GCYCLES);
    fprintf(out, "\t-o OFFSET\tUse an offset of OFFSET nodes. Sensible values"           " \n\t\t\tcould be 64 for 8 threads, 200 for 32 threads. "
	    "\n\t\t\tDefault: %i\n",
	    DEFAULT_OFFSET);
    fprintf(out, "\t-n NUM\t\tUse NUM threads. Default: %i\n",
		DEFAULT_NTHREADS);
}


int
main (int argc, char **argv) 
{
    int opt;
    gsl_rng *rng;
    
    extern char *optarg;
    extern int optind, optopt;
    int nthreads = DEFAULT_NTHREADS;
    int offset = DEFAULT_OFFSET;
    int gcycles = DEFAULT_GCYCLES;

    int initial_size = 1<<15;
    
    while ((opt = getopt(argc, argv, "t:n:o:h")) >= 0) {
	switch (opt) {
	case 'n': nthreads = atoi(optarg); break;
	case 't': gcycles  = atoi(optarg); break;
	case 'o': offset   = atoi(optarg); break;
	case 'h': usage(stdout, argv[0]); exit(EXIT_SUCCESS); break;
	}
    }

    ts = malloc(nthreads*sizeof(pthread_t));

    rng = gsl_rng_alloc(gsl_rng_mt19937);
    gsl_rng_set(rng, time(NULL));

    _init_gc_subsystem();
    pq = pq_init(offset);

    uint64_t elem;
    for (int i = 0; i < initial_size; i++) {
	elem = (uint64_t) gsl_rng_get(rng);
	insert(pq, elem, (void *)elem);
    }


    /* RUN the workloads */
    for (long i = 0; i < nthreads; i++) {
	pthread_create(&ts[i], NULL, run, (void *)i);
    }

    end = gcycles * 1000000000UL + NOW();
    IWMB();
    
    start = 1;
    
    
    /* JOIN them */
    for (int i = 0; i < nthreads; i++)
	pthread_join(ts[i], NULL);


    printf("%d\n", measure);
    
    /* FREE */
    pq_destroy(pq);
    free (rng);
    free (ts);
    _destroy_gc_subsystem();
    free(pq);
}


__thread gsl_rng *rng;
__thread long id;

inline int __attribute__((always_inline))
work (pq_t *pq)  
{
    uint64_t elem = (uint64_t) gsl_rng_get(rng);

    if (gsl_rng_uniform(rng) < 0.5) {
	insert(pq, elem, (void *)elem);
    } else {
	deletemin(pq);
    }
    return 1;
}

void *
run (void *_args)
{
    id = (long)_args;
    int cnt = 0;

#ifdef PIN
    /* Straight allocation on 32 core machine.
     * Check with your OS + machine.  */
    pin (gettid(), id/8 + 4*(id % 8));
#endif

    rng = gsl_rng_alloc(gsl_rng_mt19937);
    gsl_rng_set(rng, time(NULL)+id); 


    // wait
    while (!start);
    
    do {
        /* BEGIN work */
	work(pq);
        cnt++;
	/* END work */
    } while (NOW() < end);
    /* end of measured execution */

    gsl_rng_free(rng);
    __sync_fetch_and_add(&measure, cnt);
    //printf("bailing out: %d, %d\n", id, cnt);
    
    return NULL;
}

