/*************************************************************************
 * prioq.c
 * 
 * Lock-free concurrent priority queue.
 *
 * Copyright (c) 2012-2013, Jonatan Linden
 * with parts copyright (c) 2001-2003, Keir Fraser
 * All rights reserved.
 * 
 * Adapted from Keir Fraser's skiplist, available at 
 * http://www.cl.cam.ac.uk/research/srg/netos/lock-free/.
 *
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 
 *  * Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 * 
 *  * The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
locate_preds(pq_t *pq, pkey_t k, node_t **pa, node_t **na)
{
    node_t *x, *x_next;
    int skew = 0, d = 0;

    int i = NUM_LEVELS - 1;
    x = pq->head;

    while (i >= 0)
    {
	x_next = x->next[i];
	d = is_marked_ref(x_next);
	x_next = get_unmarked_ref(x_next);
        while (x_next->k < k || is_marked_ref(x_next->next[0]) 
	       || ((i == 0) && d)) {
	    if (i < (NUM_LEVELS - 1) && (x_next == na[i+1])) {
		skew = 1;
	    }
	    x = x_next;
	    __sync_synchronize();
	    x_next = x->next[i];
	    d = is_marked_ref(x_next);
	    x_next = get_unmarked_ref(x_next);
	}
        if ( pa ) pa[i] = x;
        if ( na ) na[i] = x_next;
	i--;
    }
    return skew;
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
    t->level = NUM_LEVELS;
    
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
insert(pq_t *pq, pkey_t k, val_t v)
{
    node_t *preds[NUM_LEVELS], *succs[NUM_LEVELS];
    node_t *pred, *succ, *new = NULL;
    int        i, level, skew = 0;

    critical_enter();
    
    /* Initialise a new node for insertion. */
    new    = alloc_node(pq);
    new->k = k;
    new->v = v;
    level = new->level;

retry:

    skew = locate_preds(pq, k, preds, succs);
    succ = succs[0];
    pred = preds[0];

    if (succ->k == k && !is_marked_ref(pred->next[0]) && pred->next[0] == succ) {
	free_node(new);
	goto success;
    }

    new->next[0] = succ;
    IWMB();
    
    
    /* We've committed when we've inserted at the bottom level. */
    if (!__sync_bool_compare_and_swap(&preds[0]->next[0], succ, new)) {
	/* either succ has been deleted (modifying preds[0]),
	 * or another insert has succeeded */
	goto retry;
    }


    /* Insert at each of the other levels in turn. */
    i = 1;
    
    while ( i < level && !skew)
    {
        pred = preds[i];
	succ = succs[i];

	/* if successor of new is deleted, we're done */
	if (is_marked_ref(new->next[0])) {
	    goto success;
	}
	

	new->next[i] = succ;
	IWMB();
	
        if (!__sync_bool_compare_and_swap(&pred->next[i], succ, new))
        {
	    /* competing insert */
            skew = locate_preds(pq, k, preds, succs);

	    if (succs[0] != new) {
		goto success;
	    }
	    
        } else {
	    /* Succeeded at this level. */
	    i++;
	}
	
    }
success:
    if (new) {
	new->inserting = 0;
	IWMB();
    }
    
    critical_exit();
}



void
restructure(pq_t *pq)
{
    node_t *pred, *cur, *h;
    int i = NUM_LEVELS - 1;
    pred = pq->head;
    while (i > 0) {
	h = pq->head->next[i];
	IRMB();
	cur = pred->next[i];
	if (!is_marked_ref(h->next[0])) {
	    i--;
	    continue;
	}
	while(is_marked_ref(cur->next[0])) {
	    pred = cur;
	    cur = pred->next[i];
	    IRMB();
	}
	if (__sync_bool_compare_and_swap(&pq->head->next[i],h,pred->next[i]))
	    i--;
    }
}
/*
void
wie_restructure (pq_t *pq)
{
    int i = NUM_LEVELS -1;

    while (i > 0) {
	node_t *next = l->head->next[i];
	while (next != CASPO(&l->head->next[i], next, preds[i]->next[i]))
	{
	    // we have a new beginning of the list.
	    search_end(l, preds, i);
	    next = l->head->next[i];
	}
    }
    for (int i = start_lvl; i >= 1; i-- )
    {
	for ( ; ; )
	{
	    x_next = get_unmarked_ref(x->next[i]);
	    if (!is_marked_ref(x_next->next[0])) break;
	    x = x_next;
	    assert(x != END);
	}
	pa[i] = x;
    }
}
*/

/*
void
old_restructure(pq_t *pq)
{
    node_t *preds[NUM_LEVELS], *succs[NUM_LEVELS], *hs[NUM_LEVELS];
    node_t *pred, *cur;
    for (int i = NUM_LEVELS - 1; i > 0; i--)
    {
	hs[i] = pq.head->next[i];
    }
    locate_preds(pq, 0, preds, succs);

    int level = NUM_LEVELS - 1;
    while (level > 0) {
	if (__sync_bool_compare_and_swap(&pq->head->next[i],hs[i],preds[i]->next[i])) {
	    i--;
	}
    }
}
*/


pkey_t
deletemin(pq_t *pq)
{
    val_t   v = NULL;
    pkey_t   k = 0;
    node_t *preds[NUM_LEVELS];
    node_t *x, *nxt, *observed_hp, *newhead, *nxt_ref;
    int offset, lvl;
    
    newhead = NULL;
    offset = lvl = 0;

    critical_enter();
    
    x = pq->head;
    observed_hp = x->next[0];

    do {
	offset++;

	IRMB();
	nxt = x->next[0]; // expensive

	if (nxt == pq->tail){
	    k = KEY_NULL; // tail cannot be deleted
	    goto out;
	}
	
	nxt_ref = get_unmarked_ref(nxt);
	if (newhead == NULL && nxt_ref->inserting) {
	    newhead = nxt_ref;
	}

	if (is_marked_ref(nxt)) continue;
	/* the marker is on the preceding pointer */
	/* linearisation */
	nxt = __sync_fetch_and_or((node_t **)&x->next[0], 1);
    }
    while ( is_marked_ref(nxt) && (x = get_unmarked_ref(nxt)));

    assert(!is_marked_ref(nxt));
    x = nxt;

    /* save value */
    v = x->v;
    k = x->k;
    
    if (newhead == NULL)
	newhead = x;
    /* if the offset is big enough, try to update and perform memory reclamation */
    if (offset <= pq->max_offset || pq->head->next[0] != observed_hp || get_marked_ref(newhead) == observed_hp) goto out;

    /* try to swing the hp to the new dummy node x, which is deleted */
    if (__sync_bool_compare_and_swap(&pq->head->next[0], observed_hp, get_marked_ref(newhead)))
    {
	/* Update higher level pointers. */

	restructure(pq);

	/* We successfully swung the top head pointer. Recycle all
	 * nodes between the head pointer and the new logical head. */
	nxt = get_unmarked_ref(observed_hp);
	while (nxt != get_unmarked_ref(newhead)) {
	    free_node(nxt);
	    nxt = get_unmarked_ref(nxt->next[0]);

	}
    }
out:
    critical_exit();
    return k;
}

void sequential_length(pq_t *pq) {
    node_t *x, *nxt;
    int cnt_del = 0, cnt = 0;
    
    x = pq->head;
    while (1)
    {
	nxt = x->next[0];
	if (nxt = pq->tail) goto out;
	if (is_marked_ref(nxt)) {
	    cnt_del++;
	} else {
	    cnt++;
	}
 	nxt = get_unmarked_ref(nxt);
    }
out:
    printf("length: %d, of which %d deleted.\n", cnt+cnt_del, cnt_del);
    
}
