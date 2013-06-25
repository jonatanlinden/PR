/*************************************************************************
 * prioq.c
 * 
 * Priority queue, allowing concurrent update by use of CAS primitives. 
 * 
 * Heavily relying on work by K A Fraser
 * Copyright (c) 2001-2003, K A Fraser
 * Copyright (c) 2013-2016, Jonatan Linden
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


#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <inttypes.h>
#include <gsl/gsl_randist.h>
#include "portable_defns.h"
#include "prioq.h"
#include "ptst.h"
#include "j_util.h"


__thread ptst_t *ptst;
__thread unsigned int randomSeed = 34243111;// = (unsigned int) read_tsc_p();

static int gc_id[NUM_LEVELS];


/*
 * Allocate a new node, and initialise its @level field.
 */
static node_t *
alloc_node(set_t *q)
{
    node_t *n;
    unsigned int x = randomSeed;
    x ^= x << 13;
    x^= x >> 17;
    randomSeed = x ^= x << 5;
    int level = 1;
    while (((x >>= 1) & 1) != 0) 
	++level;
    
    //unsigned int l = gsl_ran_geometric(ptst->rng, 0.5);
    level = (level < 20) ? level : 20;
    n = gc_alloc(ptst, gc_id[level - 1]);
    n->level = level;
    n->inserting = 1;
    return n;
}


/* Free a node to the garbage collector. */
static inline void 
free_node(node_t *n)
{
    gc_free(ptst, (void *)n, gc_id[(n->level) - 1]);
}

static int
search_end(set_t *l, node_t **pa, int toplvl)
{
    node_t *x, *x_next;
    setkey_t  x_next_k;
    int lvl = 0;
    int start_lvl = toplvl == -1 ? NUM_LEVELS - 1 : toplvl;
    if (toplvl > 0) lvl = toplvl;
    
    x = l->head;
    for (int i = start_lvl; i >= 1; i-- )
    {
        for ( ; ; )
        {
	    x_next = get_unmarked_ref(x->next[i]);
	    if (!is_marked_ref(x_next->next[0])) break;

	    /* first lvl that actually needs updating */
	    if (!lvl) lvl = i;
	    
            x = x_next;
	    assert(x != END);
	}

        pa[i] = x;
    }
    return lvl;
}

/*
 * Search for first N, with key >= @k at each level in @l.
 * RETURN VALUES:
 *  Array @pa: @pa[i] is non-deleted predecessor of N at level i
 *  Array @na: @na[i] is N itself, which should be pointed at by @pa[i]
 *  MAIN RETURN VALUE: same as @na[0].
 */
/* This function does not remove marked nodes. Use it optimistically. */
static node_t *
search_predecessors(set_t *l, setkey_t k, node_t **pa, node_t **na, int skip)
{
    node_t *x, *x_next;

restart:
    x = l->head;
    for (int i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        for ( ; ; )
        {
            x_next = x->next[i];
            x_next = get_unmarked_ref(x_next);
	    
	    /* Different strategies depending on allowing multiple keys */
	    //if ( x_next->k >= k) {
            if ( x_next->k > k || (skip && x_next->k == k)) {
		if (is_marked_ref(x->next[0]) && x_next != l->tail) {
		    if (i == 0 && x_next->k != KEY_MIN) {
			    x_next->k = KEY_MIN;
			    goto restart;
		    }
		    x = x_next;
		    continue;
		} else {
		    break;
		}
	    }

	    assert (x_next != l->tail);
            x = x_next;
	}

        if ( pa ) pa[i] = x;
        if ( na ) na[i] = x_next;
    }
    return x;
}


/*
 * PUBLIC FUNCTIONS
 */

set_t *
set_alloc(int max_offset, int max_level, int nthreads)
{
    set_t *l;
    node_t *t, *h;
    int i;

    t = malloc(63+sizeof(node_t) + (NUM_LEVELS-1)*sizeof(node_t *));
    t = (node_t *) (((uintptr_t)t+63) & ~(size_t)0x3F);
    memset(t, 0, sizeof(node_t) + (NUM_LEVELS-1)*sizeof(node_t *));
    h = malloc(63+sizeof(node_t) + (NUM_LEVELS-1)*sizeof(node_t *));
    h = (node_t *) (((uintptr_t)h+63) & ~(size_t)0x3F);
    memset(h, 0, sizeof(*h) + (NUM_LEVELS-1)*sizeof(node_t *));

    assert(((unsigned long)t & 0x3FLU) == 0);
    assert(((unsigned long)h & 0x3FLU) == 0);

    t->k = SENTINEL_KEYMAX;
    h->k = SENTINEL_KEYMIN;
    h->level = NUM_LEVELS;
    for ( i = 0; i < NUM_LEVELS; i++ )
    {
        h->next[i] = t;
    }    

    /*
     * Note use of 0xfe -- that doesn't look like a marked value!
     */
#ifdef USE_FAA
    memset(t->next, 0xc0, NUM_LEVELS*sizeof(node_t *));
#else
    memset(t->next, 0xfe, NUM_LEVELS*sizeof(node_t *));
#endif

    l = malloc(sizeof(*l) + (NUM_LEVELS-1)*sizeof(node_t *));
    l->randomSeed = (unsigned int) read_tsc_p();
    l->head = h;
    l->tail = t;
    l->max_offset = max_offset;
    l->max_level  = max_level;
    l->nthreads = nthreads;

    printf("nodesize: %d\n", (int) sizeof(node_t));

    return l;
}

__thread int cnt = 0;

void 
set_update(set_t *l, setkey_t k, setval_t v)
{
    node_t *preds[NUM_LEVELS], *succs[NUM_LEVELS];
    node_t *pred, *succ, *new = NULL, *new_next, *old_next;
    int        i, level;
    node_t *x, *x_next;
    
    critical_enter();
    
 retry:
    search_predecessors(l, k, preds, succs, 1);
    succ = succs[0];
    pred = preds[0];

    if (succ->k == k && !is_marked_ref(pred->next[0]) && pred->next[0] == succ) {
	cnt++;
	if(!(cnt%100000)){
	    printf("clashes: %d\n", cnt);
	    
	}
	goto success;
    }

    /* Initialise a new node for insertion. */
    if ( new == NULL )
    {
        new    = alloc_node(l);
        new->k = k;
        new->v = v;
    }
    level = new->level;

    /* If successors don't change, this saves us some CAS operations. */
    for ( i = 0; i < level; i++ )
    {
        new->next[i] = succs[i];
    }

    /* We've committed when we've inserted at level 1. */
    WMB_NEAR_CAS(); /* make sure node fully initialised before inserting */
    old_next = CASPO(&preds[0]->next[0], succ, new);

    if ( old_next != succ )
    {
	/* either succ has been deleted (modifying preds[0]),
	 * or another insert has succeeded */
	goto retry;
    }
    /* Insert at each of the other levels in turn. */
    i = 1;
    while ( i < level )
    {
        pred = preds[i];
        succ = succs[i];

	if (is_marked_ref(new->next[0])) {
	    goto success;
	}


	// new was live after preds recorded
	if (succ->k == KEY_MIN) {
            search_predecessors(l, k, preds, succs, 0);
	    succ = succs[0];
	    if (succ != new) goto success;
            continue;
        }


        /* Replumb predecessor's forward pointer. */
	new->next[i] = succ;
        old_next = CASPO(&pred->next[i], succ, new);
        if ( old_next != succ )
        {
	    RMB(); /* get up-to-date view of the world. */
	    if (is_marked_ref(new->next[0])) goto success;
	    /* competing insert */
            search_predecessors(l, k, preds, succs, 0);
	    succ = succs[0];
	    if (succ != new) goto success;
            continue;
        }

        /* Succeeded at this level. */
        i++;
    }
success:
    if (new)
	new->inserting = 0;
    critical_exit();
}

// Local cache of node.
__thread node_t *pt, *old_obs_hp;
__thread int old_offset;


#define THREADOPTIM

setkey_t
set_removemin(set_t *l)
{
    setval_t   v = NULL;
    setkey_t   k = 0;
    node_t *preds[NUM_LEVELS];
    node_t *x, *cur, *x_next, *obs_hp, *newhead, *x_next_ref;
    int offset, lvl;
    
    critical_enter();

start:
    offset = lvl = 0;
#ifdef THREADOPTIM
    IRMB();
    if (old_obs_hp == l->head->next[0]) {
	x = pt;
    } else {
	x = l->head;
	old_offset = 0;
	offset = 0;
	old_obs_hp = x->next[0];
    }
#endif //THREADOPTIM

    do {
	offset++;

	IRMB();
	x_next = x->next[0]; // expensive

	if (x_next == l->tail) return SETKEY_NULL; // tail cannot be deleted
	
	x_next_ref = get_unmarked_ref(x_next);
	if (newhead == NULL && x_next_ref->inserting) {
	    newhead = x_next_ref;
	}

	if (is_marked_ref(x_next)) continue;
	/* the marker is on the preceding pointer */
	/* linearisation */
	k = x_next->k;
	x_next = FAO((node_t **)&x->next[0], 1);
    }
    while ( is_marked_ref(x_next) && (x = get_unmarked_ref(x_next)));

    assert(!is_marked_ref(x_next));
    x = x_next;

#ifdef THREADOPTIM
    pt = x;
    old_offset += offset;
    offset = old_offset;
    obs_hp = old_obs_hp;
#endif

    /* save value */
    v = x->v;
    x->k = KEY_MIN; /* reset key */
    if (newhead == NULL)
	newhead = x;
    /* if the offset is big enough, try to clean up 
     * we swing the hp to the new auxiliary node x (which is deleted) 
     */
    if (offset <= l->max_offset || l->head->next[0] != obs_hp || (offset-l->nthreads) > l->max_offset || newhead == obs_hp) goto out;

    /* fails if someone else already has updated the head node */
    if (obs_hp == CASPO(&l->head->next[0], obs_hp, get_marked_ref(x)))
    {
	
	assert(offset > l->max_offset && (offset - l->nthreads) <= l->max_offset);
	/* Here we own every node between old hp and x.	 */
	/* retrieve the last deleted node for each level. */
	/* will not change. */
	lvl = search_end(l, preds, -1);

	// update upper levels
	for (int i = lvl; i > 0; i--) {
	    node_t *next = l->head->next[i];
	    while (next != CASPO(&l->head->next[i], next, preds[i]->next[i]))
	    { 
		// we have a new beginning of the list.
		search_end(l, preds, i);
		next = l->head->next[i];
	    }
	}
	/* We successfully swung the top head pointer.
	 * Recycle all nodes from head pointer to the new logical head. */
	x_next = get_unmarked_ref(obs_hp);
	while (x_next != get_unmarked_ref(x)) {
	    free_node(x_next);
	    x_next = get_unmarked_ref(x_next->next[0]);
	}
    }
out:
    critical_exit();
    return k;
}

unsigned int
num_digits (unsigned int i)
{
    return i > 0 ? (int) log10 ((double) i) + 1 : 1;
}

unsigned int
highest_level(set_t *l) {
    node_t *x, *x_next;
    x = l->head;
    for ( int i = l->max_level - 1; i >= 1; i-- )
    {
	x_next = x->next[i];
	if (x_next->next[0] != END)
	    return i;
	
    }
    return 0;
}

void
pprint (set_t *q)
{
    char *keyfrm = "%1.1f ";
    char *keyfrm1 = "-> %1.1f ";
    //char *keyfrm = "%3d ";
    node_t *n, *bottom;
    char *seps[] = {"-------", "----", "---", "--"};
    unsigned int lvl = highest_level(q);

    printf("\n");
    for (int i = lvl; i >= 0; i--) {
	/* start at top level */
	printf("l%2d: ", i);

	n = q->head;
	printf(keyfrm, n->k);

	

	n = get_unmarked_ref(q->head->next[i]);
	bottom = get_unmarked_ref(q->head->next[0]);
    
	/* while toplevel has not reached end node... */
	while (n != END) {
	    /* and while bottom level has intermediate nodes */
	    while (bottom != n)
	    {
		/* print arrows */
		//printf("%s", seps[1 -1 ]);
		printf("-------");
		
		bottom = get_unmarked_ref(bottom->next[0]);
	    }
	    /* bottom == n */
	    
	    printf(keyfrm1, n->k);
	    
	    bottom = get_unmarked_ref(bottom->next[0]);
	    n = get_unmarked_ref(n->next[i]);
	}
	printf(" -|\n");
    }

    printf("top: ");
    n = q->head;
    while (n != END) {
	printf(" t%2d,d%d", (int) n->level, is_marked_ref(n->next[0]));
	n = get_unmarked_ref(n->next[0]);
    }
    printf("\n\n");
    
}

void
seq_test ()
{
    _init_gc_subsystem();
    _init_set_subsystem();

    set_t *q = set_alloc(5, 6, 1);

    set_update(q, (double)5.1, (void *)5);
    set_update(q, (double)7, (void *)7);
    set_removemin(q);
    set_update(q, 6, (void *)6);
    set_update(q, 4, (void *)4);
    set_removemin(q);
    set_update(q, 10, (void *)10);
    set_update(q, 9, (void *)9);

    set_update(q, 4, (void *)4);
    set_removemin(q);
    set_removemin(q);
    set_removemin(q);
    set_update(q, 4, (void *)4);
    pprint(q);
    set_removemin(q);
    pprint(q);
    
}

void sequential_length(set_t *l) {
    node_t *x, *x_next;
    int cnt_del = 0, cnt = 0;
    
    x = l->head;
    while (1)
    {
	x_next = x->next[0];
	if (is_marked_ref(x_next)) {
	    cnt_del++;
	} else {
	    cnt++;
	}
 	x_next = get_unmarked_ref(x_next);
	
	// tail?
	if ( x_next == 0xfefefefefefefefe) goto out;
	x = x_next;
	
    }
out:
    printf("length: %d, of which %d deleted.\n", cnt+cnt_del, cnt_del);
    
}


void _init_set_subsystem(void)
{
    int i;

    for ( i = 0; i < NUM_LEVELS; i++ )
    {
	// aligned memory
        //gc_id[i] = gc_add_allocator(64*((63 + sizeof(node_t) + i*sizeof(node_t *))/64));
	gc_id[i] = gc_add_allocator(sizeof(node_t) + i*sizeof(node_t *));
	
    }
}

