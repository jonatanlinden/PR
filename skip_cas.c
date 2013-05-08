/******************************************************************************
 * skip_cas.c
 * 
 * Skip lists, allowing concurrent update by use of CAS primitives. 
 * 
 * Copyright (c) 2001-2003, K A Fraser
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

#define __SET_IMPLEMENTATION__

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <inttypes.h>
#include <gsl/gsl_randist.h>
#include "portable_defns.h"
#include "ptst.h"
#include "set.h"
#include "j_util.h"

/*
 * SKIP LIST
 */

#define KEYOFFSET 6

typedef struct node_st node_t;
typedef struct set_st set_t;
typedef VOLATILE node_t *sh_node_pt;

struct node_st
{
    int        level;
#define LEVEL_MASK     0x0ff
#define READY_FOR_FREE 0x100
    setkey_t  k;
    setval_t  v;
    sh_node_pt next[1];
};

struct set_st
{
    node_t head;
};


__thread ptst_t *ptst;
static int gc_id[NUM_LEVELS];

/*
 * PRIVATE FUNCTIONS
 */


/*
 * Allocate a new node, and initialise its @level field.
 * NB. Initialisation will eventually be pushed into garbage collector,
 * because of dependent read reordering.
 */
static node_t *alloc_node()
{
    node_t *n;
    unsigned int l = gsl_ran_geometric(ptst->rng, 0.5);
    l = (l < 20) ? l : 20;
    n = gc_alloc(ptst, gc_id[l - 1]);
    n->level = l;
    return(n);
}


/* Free a node to the garbage collector. */
static void free_node(sh_node_pt n)
{
    gc_free(ptst, (void *)n, gc_id[(n->level & LEVEL_MASK) - 1]);
}


/*
 * Search for first non-deleted node, N, with key >= @k at each level in @l.
 * RETURN VALUES:
 *  Array @pa: @pa[i] is non-deleted predecessor of N at level i
 *  Array @na: @na[i] is N itself, which should be pointed at by @pa[i]
 *  MAIN RETURN VALUE: same as @na[0].
 */
static sh_node_pt strong_search_predecessors(
    set_t *l, setkey_t k, sh_node_pt *pa, sh_node_pt *na)
{
    sh_node_pt x, x_next, old_x_next, y, y_next;
    setkey_t  y_k;
    int        i;

 retry:
    RMB();

    x = &l->head;
    for ( i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        /* We start our search at previous level's unmarked predecessor. */
        READ_FIELD(x_next, x->next[i]);
        /* If this pointer's marked, so is @pa[i+1]. May as well retry. */
        if ( is_marked_ref(x_next) ) goto retry;

        for ( y = x_next; ; y = y_next )
        {
            /* Shift over a sequence of marked nodes. */
            for ( ; ; )
            {
                READ_FIELD(y_next, y->next[i]);
                if ( !is_marked_ref(y_next) ) break;
                y = get_unmarked_ref(y_next);
            }

            READ_FIELD(y_k, y->k);
            if ( y_k >= k ) break;

            /* Update estimate of predecessor at this level. */
            x      = y;
            x_next = y_next;
        }

        /* Swing forward pointer over any marked nodes. */
        if ( x_next != y )
        {
            old_x_next = CASPO(&x->next[i], x_next, y);
            if ( old_x_next != x_next ) goto retry;
        }

        if ( pa ) pa[i] = x;
        if ( na ) na[i] = y;
    }

    return(y);
}


/* This function does not remove marked nodes. Use it optimistically. */
static sh_node_pt weak_search_predecessors(
    set_t *l, setkey_t k, sh_node_pt *pa, sh_node_pt *na)
{
    sh_node_pt x, x_next;
    setkey_t  x_next_k;
    int        i;

    x = &l->head;
    for ( i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        for ( ; ; )
        {
            READ_FIELD(x_next, x->next[i]);
            x_next = get_unmarked_ref(x_next);
	    
	    assert(x_next->next[0] != x);


            READ_FIELD(x_next_k, x_next->k);
            if ( x_next_k >= k ) break;

            x = x_next;
        }

        if ( pa ) pa[i] = x;
        if ( na ) na[i] = x_next;
    }

    return(x_next);
}


/*
 * Mark @x deleted at every level in its list from @level down to level 1.
 * When all forward pointers are marked, node is effectively deleted.
 * Future searches will properly remove node by swinging predecessors'
 * forward pointers.
 */
static void mark_deleted(sh_node_pt x, int level)
{
    sh_node_pt x_next;

    while ( --level >= 0 )
    {
        x_next = x->next[level];
        while ( !is_marked_ref(x_next) )
        {
            x_next = CASPO(&x->next[level], x_next, get_marked_ref(x_next));
        }
        WEAK_DEP_ORDER_WMB(); /* mark in order */
    }
}


static int check_for_full_delete(sh_node_pt x)
{
    int level = x->level;
    return ((level & READY_FOR_FREE) ||
            (CASIO(&x->level, level, level | READY_FOR_FREE) != level));
}


static void do_full_delete(set_t *l, sh_node_pt x, int level)
{
    int k = x->k;
    (void)strong_search_predecessors(l, k, NULL, NULL);
    free_node(x);
}


/*
 * PUBLIC FUNCTIONS
 */

set_t *set_alloc(int max_offset, int max_level)
{
    set_t *l;
    node_t *n;
    int i;

    n = malloc(sizeof(*n) + (NUM_LEVELS-1)*sizeof(node_t *));
    memset(n, 0, sizeof(*n) + (NUM_LEVELS-1)*sizeof(node_t *));
    n->k = SENTINEL_KEYMAX;

    /*
     * Set the forward pointers of final node to other than NULL,
     * otherwise READ_FIELD() will continually execute costly barriers.
     * Note use of 0xfe -- that doesn't look like a marked value!
     */
    memset(n->next, 0xfe, NUM_LEVELS*sizeof(node_t *));

    l = malloc(sizeof(*l) + (NUM_LEVELS-1)*sizeof(node_t *));
    l->head.k = SENTINEL_KEYMIN;
    l->head.level = NUM_LEVELS;
    for ( i = 0; i < NUM_LEVELS; i++ )
    {
        l->head.next[i] = n;
    }

    return(l);
}


setval_t set_update(set_t *l, setkey_t k, setval_t v)
{
    setval_t  ov, new_ov;
    sh_node_pt preds[NUM_LEVELS], succs[NUM_LEVELS];
    sh_node_pt pred, succ, new = NULL, new_next, old_next;
    int        i, level;
    static int cnt = 0;
    
    k = k << KEYOFFSET; // fit duplicates.

    critical_enter();

    succ = weak_search_predecessors(l, k, preds, succs);
    
 retry:

    /* Not in the list, so initialise a new node for insertion. */
    if ( new == NULL )
    {
        new    = alloc_node();
        new->k = k;
        new->v = v;
    }

    if ( succ->k == k )
    {
	
	k++;
	new->k = k;
	/* Will fail if same key is inserted 2^KEYOFFSET times */
	assert(k % (1<<KEYOFFSET) != 0);
	
	i = 0;
	while (i < (succ->level & LEVEL_MASK)) {

	    preds[i] = succ;
	    RMB();
	    
	    succs[i] = get_unmarked_ref(succ->next[i]);
	    i++;
	    }
	if (succs[0]->k == k) {
	    succ = succs[0];
	    goto retry;
	    }
	while (i < new->level) {
	    RMB();
	    pred = get_unmarked_ref(preds[i]);
	    succs[i] = get_unmarked_ref(pred->next[i]);
	    if (succs[i]->k <= k) {
		cnt++;
		succ = weak_search_predecessors(l, k, preds, succs);
		goto retry;
	    }
	    i++;
	}

	succ = succs[0];
	goto retry;
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
        succ = strong_search_predecessors(l, k, preds, succs);
        goto retry;
    }

    /* Insert at each of the other levels in turn. */
    i = 1;
    while ( i < level )
    {
        pred = preds[i];
        succ = succs[i];

        /* Someone *can* delete @new under our feet! */
        new_next = new->next[i];
        if ( is_marked_ref(new_next) ) goto success;

        /* Ensure forward pointer of new node is up to date. */
        if ( new_next != succ )
        {
            old_next = CASPO(&new->next[i], new_next, succ);
            if ( is_marked_ref(old_next) ) goto success;
            assert(old_next == new_next);
        }

        /* Ensure we have unique key values at every level. */
        //if ( succ->k == k ) goto new_world_view;
	 assert((pred->k <= k) && (succ->k >= k));


        /* Replumb predecessor's forward pointer. */
        old_next = CASPO(&pred->next[i], succ, new);
        if ( old_next != succ )
        {
        new_world_view:
            RMB(); /* get up-to-date view of the world. */
            (void)strong_search_predecessors(l, k, preds, succs);
            continue;
        }

        /* Succeeded at this level. */
        i++;
    }

 success:
    /* Ensure node is visible at all levels before punting deletion. */
    WEAK_DEP_ORDER_WMB();
    if ( check_for_full_delete(new) ) 
    {
        MB(); /* make sure we see all marks in @new. */
        do_full_delete(l, new, level - 1);
    }
 out:
    
    critical_exit();
    if (!(cnt % 10000)) {
	printf("cnt: %d\n", cnt);
	cnt++;
    }

    return(ov);
}


setval_t set_remove(set_t *l, setkey_t k)
{
    setval_t  v = NULL, new_v;
    sh_node_pt preds[NUM_LEVELS], x;
    int        level, i;

    //k = CALLER_TO_INTERNAL_KEY(k);

    x = weak_search_predecessors(l, k, preds, NULL);
    if ( x->k > k ) goto out; //shouldn't happen
    READ_FIELD(level, x->level);
    level = level & LEVEL_MASK;

     /* Committed to @x: mark lower-level forward pointers. */
    WEAK_DEP_ORDER_WMB(); /* enforce above as linearisation point */
    mark_deleted(x, level);

    /*
     * We must swing predecessors' pointers, or we can end up with
     * an unbounded number of marked but not fully deleted nodes.
     * Doing this creates a bound equal to number of threads in the system.
     * Furthermore, we can't legitimately call 'free_node' until all shared
     * references are gone.
     */
    for ( i = level - 1; i >= 0; i-- )
    {
        if ( CASPO(&preds[i]->next[i], x, get_unmarked_ref(x->next[i])) != x )
        {
            if ( (i != (level - 1)) || check_for_full_delete(x) )
            {
                MB(); /* make sure we see node at all levels. */
                do_full_delete(l, x, i);
            }
            goto out;
        }
    }

    free_node(x);

out:
    return(v);
}


setkey_t set_removemin(set_t *l)
{
    setkey_t  k = 0;
    setval_t  v = NULL, new_v;
    sh_node_pt preds[NUM_LEVELS];
    int        level, i;
    sh_node_pt x, x_next;
    setkey_t  x_k;
    
    critical_enter();

    x = &l->head;

    while (1)
    {
	x_next = x->next[0];
	x_next = get_unmarked_ref(x_next);
	
	// tail?
	if ( x_next == NULL || x_next == 0xfefefefefefefefe) goto out;

	/* Once we've marked the value field, the node is effectively deleted. */
	new_v = x_next->v;
	do {
	    v = new_v;
	    if ( v == NULL ) break; // continue to next node
	}
	while ( (new_v = CASPO(&x_next->v, v, NULL)) != v );

	x = x_next;
	if (v != NULL) 
	{
	    break;  //success
	}

    }
    x_k = x->k;    

    set_remove(l, x_k);

out:
    critical_exit();
    return x_k >> KEYOFFSET;
}


setval_t set_lookup(set_t *l, setkey_t k)
{
    setval_t  v = NULL;
    sh_node_pt x;

    //k = CALLER_TO_INTERNAL_KEY(k);

    critical_enter();

    x = weak_search_predecessors(l, k, NULL, NULL);
    if ( x->k == k ) READ_FIELD(v, x->v);

    critical_exit();
    return(v);
}


void _init_set_subsystem(void)
{
    int i;

    for ( i = 0; i < NUM_LEVELS; i++ )
    {
        gc_id[i] = gc_add_allocator(sizeof(node_t) + i*sizeof(node_t *));
    }
}
