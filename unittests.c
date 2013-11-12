#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>
#include <assert.h>
#include <pthread.h>
#include <inttypes.h>
#include <gsl/gsl_rng.h>

#include "gc/gc.h"

#include "prioq.h"
#include "common.h"

static pq_t *pq;

#define PER_THREAD 30

int nthreads;

pthread_t *ts;


void *add_thread(void *id);
void *removemin_thread(void *id);
void *invariant_thread(void *id);

node_t *stack[32];
int stack_idx = 0;

void
push(node_t *n) 
{
    stack[stack_idx++] = n;
}

node_t *
pop() 
{
    assert(stack_idx > 0);
    return stack[--stack_idx];
}

node_t *
peek()
{
    assert(stack_idx > 0);
    return stack[stack_idx - 1];
}


void test_parallel_add() {

    printf("test parallel add, %d threads\n", nthreads);

    for (long i = 0; i < nthreads; i ++)
    {
        pthread_create (&ts[i], NULL, add_thread, (void *)i);
    }

    for (long i = 0; i < nthreads; i ++)
    {
	(void)pthread_join (ts[i], NULL);
    }
    
    int new, old = -1;
    for (long i = 0; i < nthreads * PER_THREAD; i++) {
	new = deletemin(pq);
	assert (old < new);
	old = new;
    }
    
    printf("OK.\n");
}


void test_parallel_del() {

    printf("test parallel del, %d threads\n", nthreads);

    for (long i = 0; i < nthreads * PER_THREAD; i++) {
	insert(pq, i, (val_t)i);
    }


    for (long i = 0; i < nthreads; i ++)
    {
        pthread_create (&ts[i], NULL, removemin_thread, (void *)i);
    }

    for (long i = 0; i < nthreads; i ++)
    {
	(void)pthread_join (ts[i], NULL);
    }
    
    
    printf("OK.\n");
}

void
check_invariants(pq_t *pq) 
{
    
    node_t *cur, *pred;
    int curlvl, cnt = 0;
    int highest_lvl = 32;
    unsigned long long k = 0;

    
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
	assert(cur->k > k);
	k = cur->k;
	pred = cur;
	cur = pred->next[0];
	cnt++;
    }

    /* Find first level with hp not pointing at tail. */
    while(pq->head->next[--highest_lvl] == pq->tail) ;
    
    curlvl = highest_lvl;
    cur = get_unmarked_ref(pq->head->next[curlvl]);
    while(cur != pq->tail) {
	while(curlvl > 0)
	    push (cur->next[curlvl--]);
	cur = get_unmarked_ref(cur->next[0]);
	while(curlvl < highest_lvl && cur == peek()) {
	    pop();
	    curlvl++;
	}
    }
    if (curlvl != highest_lvl) {
	printf("c: %d h: %d\n", curlvl, highest_lvl);
    }
}


int halt = 0;
int stop = 0;
int abort_loop = 0;


void test_invariants() {
    for (long i = 0; i < nthreads * PER_THREAD; i++) {
	insert(pq, i, (val_t)i);
    }

    for (long i = 0; i < nthreads; i ++)
    {
        pthread_create (&ts[i], NULL, invariant_thread, (void *)i);
    }

    for (int i = 0; i < 200; i++) {
	usleep(50000);
	halt = 1;
	while(stop < nthreads) {
	    IRMB();
	}
	check_invariants(pq);
	stop = 0;
	halt = 0;
	IWMB();

    }
    abort_loop = 1;
    
    for (long i = 0; i < nthreads; i ++)
    {
	(void)pthread_join (ts[i], NULL);
    }
    
}



void setup (int max_offset) {
    _init_gc_subsystem();
    pq = pq_init(max_offset);
}

void teardown () {
    _destroy_gc_subsystem();
    free(pq);
    
}

int main(int argc, char **argv) {
    nthreads = 8;
    
    ts = malloc(nthreads * sizeof(pthread_t));
    assert(ts);


    setup(10);
    
/*    test_parallel_add();
    

    teardown();

    setup(10);
    
    test_parallel_del();
*/
    test_invariants();
    

    teardown();

    

    return 0;
}

__thread gsl_rng *rng;



void *
invariant_thread(void *_args) {
    unsigned long id = (unsigned long)_args;
    long base = PER_THREAD * id;
    uint64_t elem;
    int cnt = 0;
    

    rng = gsl_rng_alloc(gsl_rng_mt19937);
    gsl_rng_set(rng, id); 

    while(!abort_loop) {
	if (halt) {
	    __sync_fetch_and_add(&stop, 1);
	    while(halt)
		IRMB();
	    
	}
	if (gsl_rng_uniform(rng) < 0.5) {
	    elem = (uint64_t) gsl_rng_get(rng);
	    insert(pq, elem, (void *)elem);
	} else {
	    deletemin(pq);
	}
	cnt++;
    }
    printf("%d %d\n", id, cnt);
    return NULL;
}



void *
add_thread(void *id) {
    long base = PER_THREAD * (long)id;
    int x;
    for(int i = 0; i < PER_THREAD; i++) {
	x = base + i;
	insert(pq, base+i, (val_t) base+i);
	
    }
    return NULL;
}

void *removemin_thread(void *id) {
    int v, ov = -1;
    for(int i = 0; i < PER_THREAD; i++) {
	v = deletemin(pq);
	assert(v > ov);
	ov = v;
    }
    return NULL;
}


