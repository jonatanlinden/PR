#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

#include "gc/gc.h"

#include "prioq.h"
#include "common.h"

#define PER_THREAD 30

static pq_t *pq;

int nthreads;

pthread_t *ts;

void *add_thread(void *id);
void *removemin_thread(void *id);
void *invariant_thread(void *id);


/* the different tests */
void test_parallel_add(void);
void test_parallel_del(void);
void test_invariants(void);

typedef void (* test_func_t)(void);

test_func_t tests[] = {
    test_parallel_del,
    test_parallel_add,
//    test_invariants,
    NULL
};

void 
test_parallel_add() 
{
    printf("test parallel add, %d threads\n", nthreads);

    for (long i = 0; i < nthreads; i ++)
        pthread_create (&ts[i], NULL, add_thread, (void *)i);

    for (long i = 0; i < nthreads; i ++)
	(void)pthread_join (ts[i], NULL);

    unsigned long new, old = 0;
    for (long i = 0; i < nthreads * PER_THREAD; i++) {
	new = (long)deletemin(pq);
	assert (old < new);
	old = new;
    }
    
    printf("OK.\n");
}


void 
test_parallel_del() 
{
    printf("test parallel del, %d threads\n", nthreads);

    for (long i = 0; i < nthreads * PER_THREAD; i++)
	insert(pq, i+1, (pval_t)i+1);

    for (long i = 0; i < nthreads; i ++)
        pthread_create (&ts[i], NULL, removemin_thread, (void *)i);

    for (long i = 0; i < nthreads; i ++)
	(void)pthread_join (ts[i], NULL);
    
    printf("OK.\n");
}

void
check_invariants(pq_t *pq) 
{
    
    node_t *cur, *pred;
    int cnt = 0;
    unsigned long long k = 0;
    int i = 0;

    /* Bottom level */
    /* deleted prefix */
    cur = pq->head->next[0];
    while (is_marked_ref(cur)) {
	pred = get_unmarked_ref(cur);
	cur = pred->next[0];
	cnt++;
    }

    pred = cur;
    cur = pred->next[0];

    while (cur != pq->tail) {
	assert(!is_marked_ref(cur));
	i = 1;
	/* pred and succ at each each level is ordered correctly */
	while(i < cur->level && cur->next[i]) {
	    assert(cur->k < cur->next[i]->k);
	    i++;
	}
	assert(cur->k > k);
	k = cur->k;
	pred = cur;
	cur = pred->next[0];
	cnt++;
    }

    /* Higher levels */
    k = 0;
    for (int i = 31; i > 0; i--) {
	cur = get_unmarked_ref(pq->head->next[i]);
	while(cur != pq->tail) {
	    cur = get_unmarked_ref(cur->next[i]);
	}
    }
}

/* test_invariants control of invariant threads */
volatile int halt = 0, stop = 0, abort_loop = 0;

/* A rough way to test that certain invariants always are true.
 * Run a certain number of operations, halt, check invariants,
 * continue, halt, etc.
 * Specifically, it does not check that the invariants hold during
 * the execution of an operation.
 */

void
test_invariants() 
{
    printf("test invariants, %d threads\n", nthreads);
    
    for (long i = 0; i < nthreads * PER_THREAD; i++)
	insert(pq, i+1, (pval_t)i + 1);

    for (long i = 0; i < nthreads; i ++)
        pthread_create (&ts[i], NULL, invariant_thread, (void *)i);

    for (int i = 0; i < 200; i++) {
	usleep(50000);
	halt = 1;
	while(stop < nthreads) {
	    IRMB();
	}
	printf(".");
	fflush(stdout);
	check_invariants(pq);
	stop = 0;
	halt = 0;
	IWMB();

    }
    abort_loop = 1;
    
    for (long i = 0; i < nthreads; i ++)
        (void)pthread_join (ts[i], NULL);
    
    printf("\nOK.\n");
}

void
setup (int max_offset) 
{
    _init_gc_subsystem();
    pq = pq_init(max_offset);
}

void
teardown ()
{
    pq_destroy(pq);
    _destroy_gc_subsystem();
}

int
main(int argc, char **argv)
{
    nthreads = 8;

    ts = malloc(nthreads * sizeof(pthread_t));
    assert(ts);

    for(test_func_t *tf = tests; *tf; tf++) {
        setup(10);
        (*tf)();
        teardown();
    }
    
    return 0;
}

__thread unsigned short rng[3];

void *
invariant_thread(void *_args)
{
    unsigned long id = (unsigned long)_args;
    unsigned long elem;
    int cnt = 0;

    rng_init(rng);

    while(!abort_loop) {
	if (halt) {
	    __sync_fetch_and_add(&stop, 1);
	    while(halt)
		IRMB();
	}
	if (erand48(rng) < 0.5) {
	    elem = nrand48(rng);
	    insert(pq, elem+1, (pval_t)elem + 1);
	} else {
	    deletemin(pq);
	}
	cnt++;
    }
    return NULL;
}



void *
add_thread(void *id)
{
    long base = PER_THREAD * (long)id;
    for(int i = 0; i < PER_THREAD; i++)
	insert(pq, base+i+1, (pval_t) base+i+1);
    return NULL;
}


void *
removemin_thread(void *id)
{
    unsigned long v, ov = 0;
    for(int i = 0; i < PER_THREAD; i++) {
	v = (unsigned long) deletemin(pq);
	assert(v > ov);
	ov = v;
    }
    return NULL;
}


