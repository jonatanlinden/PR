#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>
#include <assert.h>
#include <pthread.h>

#include "prioq.h"
#include "gc.h"

static pq_t *pq;

#define PER_THREAD 30

int nthreads;

pthread_t *ts;


void *add_thread(void *id);
void *removemin_thread(void *id);


int test_parallel_add() {

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


int test_parallel_del() {

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



int setup (int max_offset) {
    _init_gc_subsystem();
    pq = pq_init(max_offset);
}

int teardown () {
    _destroy_gc_subsystem();
    free(pq);
    
}

int main(int argc, char **argv) {
    nthreads = 8;
    
    ts = malloc(nthreads * sizeof(pthread_t));
    assert(ts);

    setup(10);
    
    test_parallel_add();
    

    teardown();

    setup(10);
    
    test_parallel_del();
    

    teardown();

    

    return 0;
}



void *
add_thread(void *id) {
    long base = PER_THREAD * (long)id;
    int x;
    for(int i = 0; i < PER_THREAD; i++) {
	x = base + i;
	insert(pq, base+i, (val_t) base+i);
	
    }
}

void *removemin_thread(void *id) {
    int v, ov = -1;
    for(int i = 0; i < PER_THREAD; i++) {
	v = deletemin(pq);
	assert(v > ov);
	ov = v;
    }
}


