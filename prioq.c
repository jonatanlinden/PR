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
#include <stdint.h>
#include "portable_defns.h"
#include "ptst.h"
#include "set.h"
#include "j_util.h"

/*
 * SKIP LIST
 */

typedef struct node_st node_t;
typedef struct set_st set_t;
typedef VOLATILE node_t *sh_node_pt;

struct node_st
{
    setkey_t  k;
    int       level;
    setval_t  v;
#define LEVEL_MASK     0x0ff
#define READY_FOR_FREE 0x100
    char pad0[88]; // increases perf.
    sh_node_pt next[1];
};

struct set_st
{
    int max_offset;
    node_t head;
};

static int gc_id[NUM_LEVELS];

/*
 * PRIVATE FUNCTIONS
 */

/*
 * Random level generator. Drop-off rate is 0.5 per level.
 * Returns value 1 <= level <= NUM_LEVELS.
 */
static int get_level(ptst_t *ptst)
{
    unsigned long r = rand_next(ptst);
    int l = 1;
    r = (r >> 4) & ((1 << (NUM_LEVELS-1)) - 1);
    while ( (r & 1) ) { l++; r >>= 1; }
    return(l);
}


/*
 * Allocate a new node, and initialise its @level field.
 * NB. Initialisation will eventually be pushed into garbage collector,
 * because of dependent read reordering.
 */
static node_t *alloc_node(ptst_t *ptst)
{
    int l;
    node_t *n;
    l = get_level(ptst);
    n = gc_alloc(ptst, gc_id[l - 1]);
    //n = ALIGNED_ALLOC(sizeof (node_t) + (l-1)*sizeof(sh_node_pt));
    
    n->level = l;
    
    return(n);
}


/* Free a node to the garbage collector. */
static void free_node(ptst_t *ptst, sh_node_pt n)
{
    //gc_free(ptst, (void *)n, gc_id[(n->level & LEVEL_MASK) - 1]);
}



static sh_node_pt weak_search_head(
    set_t *l)
{
    sh_node_pt x, x_next;
    setkey_t  x_next_k;
    int        i;
    x = &l->head;
    for ( i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        for ( ; ; )
        {
            x_next = x->next[i]; 
            x_next = get_unmarked_ref(x_next);

	    if (!is_marked_ref(x_next->next[0])) break;
            //x_next_k = x_next->k;
            //if ( x_next_k > 1 ) break;

            x = x_next;
	}
    }
    return x_next;
}


static int weak_search_end(set_t *l, sh_node_pt *pa, int toplvl)
{
    sh_node_pt x, x_next;
    setkey_t  x_next_k;
    int        i;
    int lvl = 0;
    int start_lvl = toplvl == -1 ? NUM_LEVELS - 1 : toplvl;
    if (toplvl > 0) lvl = toplvl;
    
    x = &l->head;
    for ( i = start_lvl; i >= 0; i-- )
    {
        for ( ; ; )
        {
            x_next = x->next[i]; 
            x_next = get_unmarked_ref(x_next);

	    if (!is_marked_ref(x_next->next[0])) break;
            
	    /* first lvl that is actual to update */
	    if (!lvl) lvl = i;

            x = x_next;
	    //assert(x != 0xfefefefefefefefe);
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
static sh_node_pt weak_search_predecessors(
    set_t *l, setkey_t k, sh_node_pt *pa, sh_node_pt *na)
{
    sh_node_pt x, x_next;
    setkey_t  x_next_k;
    int        i;
restart:
    x = &l->head;
    for ( i = NUM_LEVELS - 1; i >= 0; i-- )
    {
        for ( ; ; )
        {
            x_next = x->next[i];
            x_next = get_unmarked_ref(x_next);

            x_next_k = x_next->k;
            if ( x_next_k > k ) break;

            x = x_next;
	}

        if ( pa ) pa[i] = x;
        if ( na ) na[i] = x_next;
    }

    if ( pa && is_marked_ref(pa[0])) {
        printf("restart\n");
        goto restart;
    }

    return(x_next);
}






/*
 * PUBLIC FUNCTIONS
 */

set_t *set_alloc(int max_offset)
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

    l->max_offset = max_offset;
    

    return(l);
}



setval_t set_update(set_t *l, setkey_t k, setval_t v, int overwrite, int id)
{
    setval_t  ov, new_ov;
    ptst_t    *ptst;
    sh_node_pt preds[NUM_LEVELS], succs[NUM_LEVELS];
    sh_node_pt pred, succ, new = NULL, new_next, old_next;
    int        i, level;
    sh_node_pt x, x_next;
    int loop0;
    
    k = CALLER_TO_INTERNAL_KEY(k);
    ptst = critical_enter();

    succ = weak_search_predecessors(l, k, preds, succs);

 retry:
    loop0 = 0;
    ov = NULL;

    /* Not in the list, so initialise a new node for insertion. */
    if ( new == NULL )
    {
        new    = alloc_node(ptst);
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
	//TODO: FIX
	if (is_marked_ref(preds[0]->next[0])) {
	    new->level = 1;
	    x = get_unmarked_ref(preds[0]->next[0]);
	    do {
		loop0 ++;
		if (loop0 > 10) {
		    x = weak_search_head(l);
		    loop0 = 0;
		}
		x_next = x->next[0];
		if (!is_marked_ref(x_next)) {
		    /* The marker is on the preceding pointer. 
		     * Let's try to squeeze in here. */
		    new->next[0] = x_next;
		    if((old_next = CASPO(&x->next[0], x_next, new)) == x_next)
		    {
			if (loop0 > 5){
			    printf("Contended queue: %d\n", loop0);
			}
			goto success;
		    }
		} 
		x = get_unmarked_ref(x_next);
	    } while(1);
	} else {
	    /* competing insert. */
	    succ = weak_search_predecessors(l, k, preds, succs);
	    goto retry;
	}
    }
    
    
    /* Insert at each of the other levels in turn. */
    i = 1;
    while ( i < level )
    {
        pred = preds[i];
        succ = succs[i];

        /* Someone *can* delete @new under our feet! */

        if ( new->k != k) goto success;

        /* Ensure forward pointer of new node is up to date. */
	new_next = new->next[i];
	if ( new_next != succ )
        {
            old_next = CASPO(&new->next[i], new_next, succ);
            if ( is_marked_ref(old_next) ) goto success;
            assert(old_next == new_next);
        }

        /* Ensure we have unique key values at every level. */
        assert(pred->k <= k);

        /* Replumb predecessor's forward pointer. */
        old_next = CASPO(&pred->next[i], succ, new);
        if ( old_next != succ )
        {
	    RMB(); /* get up-to-date view of the world. */
	    if (is_marked_ref(new->next[0]) || new->k != k) goto success;
	    
            succ = weak_search_predecessors(l, k, preds, succs);
	    if (succ != new) goto success;
	    
            continue;
        }

        /* Succeeded at this level. */
        i++;
    }

success:

    critical_exit(ptst);
    return(ov);
}


setkey_t set_removemin(set_t *l)
{
    setval_t   v = NULL;
    setkey_t   k = 0;
    ptst_t    *ptst;
    sh_node_pt preds[NUM_LEVELS];
    sh_node_pt x, cur, x_next, obs_hp;
    int offset = 0, lvl;
    
    ptst = critical_enter();

    x = &l->head;
    obs_hp = x->next[0];

    do {
	offset++;
	x_next = x->next[0];
	if (x_next == 0xfefefefefefefefe) goto out;// || x_next->k == SENTINEL_KEYMAX)//x_next == 0xfefefefefefefefe) 
	// TODO: check for end of list.
	if (!is_marked_ref(x_next)) { // save 1 FAO if not set. (and we expect it not to be)
	    /* the marker is on the preceding pointer */
	    x_next = FAO((sh_node_pt *)get_unmarked_ref(&x->next[0]), 1); /* linearisation */
	}
    }
    while ( is_marked_ref(x_next) && (x = get_unmarked_ref(x_next)));

    x = x_next;

    /* save value */
    v = x_next->v;
    k = x_next->k;
    if (k == SENTINEL_KEYMAX) { /* end of queue */
	dprintf("issue, end of q reached.");
	FAA(&x->next[0], ~1UL);
	k = 0;
	goto out;
    }
    /* HELP: inserts to find right place. */
    //x->k = SENTINEL_KEYMIN;

    /* if the offset is big enough, try to clean up 
     * we swing the hp to the new auxiliary node x (which is deleted) 
     */
    if (offset <= l->max_offset) goto out;

    if (CASPO(&l->head.next[0], obs_hp, get_marked_ref(x)))
    {
	/* Here we own every node between old hp and x.
	 */
	lvl = weak_search_end(l, preds, -1);
	/* bail out if next restructuring have started */
	if (preds[0] != x) goto out; 
	
	for (int i = lvl; i > 0; i--) {
	    if(!CASPO(&l->head.next[i], l->head.next[i], preds[i]->next[i])) {
		if (preds[0] != x) {
		    goto out;
		} else {
		    // someone inserted at i, refind new head.
		    weak_search_end(l, preds, i);
		    if (preds[0] != x) goto out;
		}
	    }

	}
    }
    

    //free_node(ptst, x_next);

out:
    critical_exit(ptst);
    return k;
}


void _init_set_subsystem(void)
{
    int i;

    for ( i = 0; i < NUM_LEVELS; i++ )
    {
	printf("old size: %d\n",sizeof(node_t) + i*sizeof(node_t *));
	printf("size added: %d\n",64*((63 + sizeof(node_t) + i*sizeof(node_t *))/64));
	
        gc_id[i] = gc_add_allocator(64*((63 + sizeof(node_t) + i*sizeof(node_t *))/64));
	//gc_id[i] = gc_add_allocator(sizeof(node_t) + i*sizeof(node_t *));
	
    }
}


