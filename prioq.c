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

/* The thread state. */
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


/* Mark node as ready for reclamation to the garbage 
 * collector. */
static inline void 
free_node(node_t *n)
{
    gc_free(ptst, (void *)n, gc_id[(n->level) - 1]);
}


/* Locatepreds
 * Record predecessors and non-deleted successors of key k.  If k
 * exists in list, the node will be in succs[0]

 * Variable skew indicates that some node in succs is * deleted, but
 * that this was not noticed at the relevant level.
 *
 * Skew example illustration, when locating 3. Level 1 is shifted
 * in relation to level 0, due to not noticing that s[1] is deleted
 * until level 0 is reached.
 *
 *                   p[0] 
 * p[2]  p[1]        s[1]  s[0]  s[2]
 *  |     |           |     |     |
 *  v     |           |     |     v
 *  _     v           v     |     _ 
 * | |    _           _	    v    | |
 * | |   | |    _    | |    _    | |
 * | |   | |   | |   | |   | |   | |
 *  0     1     2     4     6     7
 *  d     d     d
 *
 */

static int
locate_preds(pq_t *pq, pkey_t k, node_t **preds, node_t **succs)
{
    node_t *x, *x_next;
    int skew = 0, d = 0, i;

    x = pq->head;
    i = NUM_LEVELS - 1;
    while (i >= 0)
    {
	x_next = x->next[i];
	d = is_marked_ref(x_next);
	x_next = get_unmarked_ref(x_next);
	
        while (x_next->k < k || is_marked_ref(x_next->next[0]) 
	       || ((i == 0) && d)) {
	    if (i < (NUM_LEVELS - 1) && (x_next == succs[i+1])) {
		skew = 1;
	    }
	    x = x_next;
	    x_next = x->next[i];
	    d = is_marked_ref(x_next);
	    x_next = get_unmarked_ref(x_next);
	}
        preds[i] = x;
        succs[i] = x_next;
	i--;
    }
    assert(!is_marked_ref(succs[0]));
    return skew;
}

/*
 * Init structure, setup sentinel head and tail nodes.
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

/* Cleanup, mark all the nodes for recycling. */
void
pq_destroy(pq_t *pq)
{
    node_t *cur, *pred;
    cur = pq->head;
while (cur != pq->tail) {
	pred = cur;
	cur = get_unmarked_ref(pred->next[0]);
	free_node(pred);
    }
    free_node(cur); //tail
}


/* ** insert **
 * Insert a new node n with key k and value v.
 * The node will not be inserted if another node with key k is already
 * present in the list.
 *
 * The predecessors, preds, and successors, succs, at all levels are
 * recorded, after which the node n is inserted from bottom to
 * top. Conditioned on that succs[i] is still the successor of
 * preds[i], n will be spliced in on level i.
 *
 */
void 
insert(pq_t *pq, pkey_t k, val_t v)
{
    node_t *preds[NUM_LEVELS], *succs[NUM_LEVELS];
    node_t *new = NULL;
    int skew = 0;

    critical_enter();
    
    /* Initialise a new node for insertion. */
    new    = alloc_node(pq);
    new->k = k;
    new->v = v;


retry:
    skew = locate_preds(pq, k, preds, succs);

    /* return if key already exists, i.e., is present in a non-deleted
     * node */
    if (succs[0]->k == k && !is_marked_ref(preds[0]->next[0]) && preds[0]->next[0] == succs[0]) {
	free_node(new);
	goto success;
    }
    new->next[0] = succs[0];

    /* The node is logically inserted once it is present at the bottom
     * level. */
    if (!__sync_bool_compare_and_swap(&preds[0]->next[0], succs[0], new)) {
	/* either succ has been deleted (modifying preds[0]),
	 * or another insert has succeeded or preds[0] is head, 
	 * and a restructure operation is underway */
	goto retry;
    }

    /* Insert at each of the other levels in turn. */
    int i = 1;
    while ( i < new->level && !skew)
    {
        /* optimization (?) */
	IRMB(); 
	
	/* if successor of new is deleted, we're done */
	if (is_marked_ref(new->next[0])) goto success;

	/* prepare next pointer of new node */
	new->next[i] = succs[i];
	
        if (!__sync_bool_compare_and_swap(&preds[i]->next[i], succs[i], new))
        {
	    /* failed due to competing insert or restruct */
            skew = locate_preds(pq, k, preds, succs);

	    /* if new has been deleted, we're done */
	    if (succs[0] != new) goto success;
	    
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


/* Restructure
 *
 * Update the head node's pointers from level 1 and up. Will locate
 * the last node at each level that has the delete flag set, and set
 * the head to point to the successor of that node. After completion,
 * if operating in isolation, for each level i, it holds that
 * head->next[i-1] is before or equal to head->next[i]. 
 *
 * Illustration after:
 *
 *             h[0]  h[1]  h[2]
 *              |     |     |
 *              |     |     v
 *  _           |     v     _ 
 * | |    _     v     _	   | |
 * | |   | |    _    | |   | |
 * | |   | |   | |   | |   | |
 *  d     d
  
 */
void
restructure(pq_t *pq)
{
    node_t *pred, *cur, *h;
    int i = NUM_LEVELS - 1;

    pred = pq->head;
    while (i > 0) {
	h = pq->head->next[i]; /* record observed head */
	IRMB(); /* the order of these reads must be maintained */
	cur = pred->next[i]; /* take one step forward from pred */
	if (!is_marked_ref(h->next[0])) {
	    i--;
	    continue;
	}
	/* traverse level until non-marked node is found 
	 * pred will always have its delete flag set 
	 */
	while(is_marked_ref(cur->next[0])) {
	    pred = cur;
	    cur = pred->next[i];
	}
	/* swing head pointer */
	if (__sync_bool_compare_and_swap(&pq->head->next[i],h,pred->next[i]))
	    i--;
    }
}


/* deletemin
 * Delete element with smallest key in queue.
 * Try to update the head node's pointers, if offset > max_offset.
 */
pkey_t
deletemin(pq_t *pq)
{
    val_t   v = NULL;
    pkey_t   k = 0;
    node_t *preds[NUM_LEVELS];
    node_t *x, *nxt, *obs_head = NULL, *newhead, *cur;
    int offset, lvl;
    
    newhead = NULL;
    offset = lvl = 0;

    critical_enter();

    x = pq->head;
    obs_head = x->next[0];

    do {
	offset++;

	IRMB(); // speed optimization
        /* expensive, high probability that this cache line has
	 * been modified */
	nxt = x->next[0];

        // tail cannot be deleted
	if (get_unmarked_ref(nxt) == pq->tail) {
	    k = KEY_NULL;
	    goto out;
	}

	// Do not allow head to point past a node currently being
	// inserted.
	if (newhead == NULL && x->inserting) newhead = x;

	/* optimization */
	if (is_marked_ref(nxt)) continue;
	/* the marker is on the preceding pointer */
        /* linearisation point deletemin */
	nxt = __sync_fetch_and_or(&x->next[0], 1);
    }
    while ( (x = get_unmarked_ref(nxt)) && is_marked_ref(nxt) );

    assert(!is_marked_ref(x));

    /* save value */
    v = x->v;
    k = x->k;
    
    /* If no inserting node was traversed, then use the latest 
     * deleted node as new lowest-level head pointed node */
    if (newhead == NULL) newhead = x;

    /* if the offset is big enough, try to update the head node and
     * perform memory reclamation */
    if (offset <= pq->max_offset) goto out;

    /* Two lines: Optimization. Marginally faster */
    IRMB();
    if (pq->head->next[0] != obs_head) goto out;
    
    /* try to swing the lowest level head pointer to point to newhead,
     * which is deleted */
    if (__sync_bool_compare_and_swap(&pq->head->next[0], obs_head, get_marked_ref(newhead)))
    {
	/* Update higher level pointers. */
	restructure(pq);

	/* We successfully swung the top head pointer. Mark all nodes
	 * between the head pointer and the new head for recycling. */

	cur = get_unmarked_ref(obs_head);
	while (cur != get_unmarked_ref(newhead)) {
	    nxt = get_unmarked_ref(cur->next[0]);
	    assert(is_marked_ref(cur->next[0]));
	    free_node(cur);
	    cur = nxt;
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



