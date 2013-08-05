/*************************************************************************
 * prioq.c
 * 
 * Priority queue, allowing concurrent update by use of CAS primitives. 
 * 
 * 
 * Copyright (c) 2001-2003, K A Fraser
 * Adapted from Keir Frasers skip list.
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

#include "common.h"
#include "prioq.h"
#include "ptst.h"



__thread ptst_t *ptst;

static int gc_id[NUM_LEVELS];

/*
 * Allocate a new node, and initialise its @level field.
 * Courtesy to Doug Lea.
 */
static node_t *
alloc_node(pq_t *q)
{
    node_t *n;
    int level = 1;
    int r = ptst->seed;
    ptst->seed = r * 134775813 + 1;
    if (r < 0) {
	while ((r <<= 1) > 0)
	    ++level;
    }
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
locate_preds(pq_t *pq, pkey_t k, node_t **pa, node_t **na, int level)
{
    node_t *x, *x_next;
    int bad_flag = 0;

restart:
    x = pq->head;
    for (int i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        for ( ; ; )
        {
            x_next = x->next[i];
            x_next = get_unmarked_ref(x_next);

            if (x_next->k >= k && !is_marked_ref(x_next->next[0]))  {

		if (i == 0 && is_marked_ref(x->next[0])) {
		    if(x_next == na[1]) {
			bad_flag = 1;
		    }
		    x = x_next;
		    continue;
		}
		
		break;
	    } else {
		if (i < NUM_LEVELS - 1 && x_next == na[i+1]) {
		    bad_flag = 1;
		}
	    }
	    x = x_next;
	    
	}
        if ( pa ) pa[i] = x;
        if ( na ) na[i] = x_next;
    }
    return bad_flag;
}


/*
 * PUBLIC FUNCTIONS
 */

pq_t *
pq_init(int max_offset)
{
    pq_t *pq;
    node_t *t, *h;
    int i;

    /* align head and tail nodes */
    t = malloc(sizeof(node_t) + (NUM_LEVELS-1)*sizeof(node_t *));
    h = malloc(sizeof(node_t) + (NUM_LEVELS-1)*sizeof(node_t *));

    t->k = SENTINEL_KEYMAX;
    h->k = SENTINEL_KEYMIN;
    h->level = NUM_LEVELS;
    for ( i = 0; i < NUM_LEVELS; i++ )
        h->next[i] = t;

    pq = malloc(sizeof *pq);
    pq->head = h;
    pq->tail = t;
    pq->max_offset = max_offset;

    for (int i = 0; i < NUM_LEVELS; i++ )
	gc_id[i] = gc_add_allocator(sizeof(node_t) + i*sizeof(node_t *));

    return pq;
}

void 
insert(pq_t *l, pkey_t k, val_t v)
{
    node_t *preds[NUM_LEVELS], *succs[NUM_LEVELS];
    node_t *pred, *succ, *new = NULL, *new_next;
    int        i, level, skew;
    node_t *x, *x_next;
    
    critical_enter();
    
 retry:

    /* Initialise a new node for insertion. */
    if ( new == NULL )
    {
        new    = alloc_node(l);
        new->k = k;
        new->v = v;
    }
    level = new->level;

    skew = locate_preds(l, k, preds, succs, level);
    succ = succs[0];
    pred = preds[0];

    if (succ->k == k && !is_marked_ref(pred->next[0]) && pred->next[0] == succ) {
	goto success;
    }

    new->next[0] = succs[0];
    
    /* We've committed when we've inserted at level 1. */
    if (!__sync_bool_compare_and_swap(&preds[0]->next[0], succ, new))
	/* either succ has been deleted (modifying preds[0]),
	 * or another insert has succeeded */
	goto retry;

    
    if (skew) goto success;

    /* Insert at each of the other levels in turn. */
    i = 1;
    while ( i < level )
    {
        pred = preds[i];
        succ = succs[i];

	/* if successor of new is deleted, we're done */
	if (is_marked_ref(new->next[0])) {
	    goto success;
	}
	new->next[i] = succ;

        if (!__sync_bool_compare_and_swap(&pred->next[i], succ, new))
        {
	    //RMB(); /* get up-to-date view of the world. */
	    if (is_marked_ref(new->next[0])) goto success;
	    /* competing insert */
            skew = locate_preds(l, k, preds, succs, level);
	    if (skew) {
		goto success;
	    }
	    succ = succs[0];
	    if (succ != new) goto success;
            continue;
        }

        /* Succeeded at this level. */
        i++;
    }
success:
    if (new) {
	new->inserting = 0;
	IWMB();
    }
    
    critical_exit();
}


inline void 
restructure(pq_t *pq)
{
    node_t *cur, *h, *next;
    int i = NUM_LEVELS - 1;
    cur = pq->head;
    // update upper levels
    while (i > 0) {
	h = pq->head->next[i];
	if (h == pq->tail) {
	    i--;
	    continue;
	}
	while(1) 
	{
	    next = cur->next[i];
	    
	    if (!is_marked_ref(next->next[0]))
		break;
	    cur = next;
	}
//	while (cur->next[i] != pq->tail && is_marked_ref(cur->next[0])) {
//	    cur = cur->next[i];
//	}
	if (__sync_bool_compare_and_swap(&pq->head->next[i],h, cur->next[i]))
	    i--;
    }
}

pkey_t
deletemin(pq_t *pq)
{
    val_t   v = NULL;
    pkey_t   k = 0;
    node_t *preds[NUM_LEVELS];
    node_t *x, *cur, *x_next, *obs_hp, *newhead, *x_next_ref;
    int offset, lvl;
    
    critical_enter();
    
    x = pq->head;
    obs_hp = x->next[0];
    
start:
    offset = lvl = 0;

    do {
	offset++;

	IRMB();
	x_next = x->next[0]; // expensive

	if (x_next == pq->tail) return KEY_NULL; // tail cannot be deleted
	
	x_next_ref = get_unmarked_ref(x_next);
	if (newhead == NULL && x_next_ref->inserting) {
	    newhead = x_next_ref;
	}

	if (is_marked_ref(x_next)) continue;
	/* the marker is on the preceding pointer */
	/* linearisation */
	x_next = __sync_fetch_and_or((node_t **)&x->next[0], 1);
    }
    while ( is_marked_ref(x_next) && (x = get_unmarked_ref(x_next)));

    assert(!is_marked_ref(x_next));
    x = x_next;


    /* save value */
    v = x->v;
    k = x->k;
    
    if (newhead == NULL)
	newhead = x;
    /* if the offset is big enough, try to update and perform memory reclamation */
    if (offset <= pq->max_offset || pq->head->next[0] != obs_hp || newhead == obs_hp) goto out;

    /* try to swing the hp to the new dummy node x, which is deleted */
    if (__sync_bool_compare_and_swap(&pq->head->next[0], obs_hp, get_marked_ref(x)))
    {
	/* Update higher level pointers. */
	restructure(pq);

	/* We successfully swung the top head pointer. Recycle all
	 * nodes between the head pointer and the new logical head. */
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

void sequential_length(pq_t *pq) {
    node_t *x, *x_next;
    int cnt_del = 0, cnt = 0;
    
    x = pq->head;
    while (1)
    {
	x_next = x->next[0];
	if (x_next = pq->tail) goto out;
	if (is_marked_ref(x_next)) {
	    cnt_del++;
	} else {
	    cnt++;
	}
 	x_next = get_unmarked_ref(x_next);
    }
out:
    printf("length: %d, of which %d deleted.\n", cnt+cnt_del, cnt_del);
    
}
