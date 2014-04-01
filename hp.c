#define _GNU_SOURCE
#include <glib.h>
#include <stdlib.h>
#include <glib.h>
#include <stdio.h>
#include "hp.h"


__thread GSList *rlist = NULL;
__thread int cnt = 0;

hp_t *
hp_init(int const K, int const nthreads, void (* hp_node_destructor)(void *))
{
    hp_t *h;
    h = malloc(sizeof(hp_t));
    
    h->K = K;
    h->nthreads = nthreads;
    h->hp_node_destructor = hp_node_destructor;
    h->cnt = 0;
    h->recs = malloc(h->nthreads * sizeof(hp_rec_t));
    
    for (int i = 0; i < nthreads; i++) {
	h->recs[i].node = malloc(h->K * sizeof(void *));
        h->recs[i].peek = malloc(h->K * sizeof(void *));
    }
    return h;
}

void 
hp_destroy(hp_t *h)
{
    printf("A total of %d nodes were recycled by hp.\n", h->cnt);
    for (int i = 0; i < h->nthreads; i++) {
	free(h->recs[i].node);
	free(h->recs[i].peek);
    }
    free(h->recs);
    free(h);
}

void
scan (hp_t *hp)
{
    GSList *plist = NULL, *iterator = NULL;
    void *tmp;
    
    /* Step 1:
     * plist will contain all nodes currently in use somewhere. */    
    for (int i = 0; i < hp->nthreads; i++) 
    {
	for (int j = 0; j < hp->K; j++)
	{
	    tmp = hp->recs[i].node[j];
	    if (NULL != tmp) {
		plist = g_slist_prepend(plist, tmp);
	    } 
            tmp = hp->recs[i].peek[j];
            if (NULL != tmp) {
		plist = g_slist_prepend(plist, tmp);
	    }
	}
    }

    /* Step 2:
     * Free all nodes in my retire list that is not in plist (i.e., not
     * in use anywhere). */
    iterator = rlist;
    while(iterator) {
	tmp = iterator->data;
	iterator = iterator->next;
    
	if (!g_slist_find(plist, tmp))
	{
	    rlist = g_slist_remove(rlist, tmp);
	    cnt--;
	    hp->hp_node_destructor(tmp);
	    __sync_fetch_and_add(&hp->cnt, 1);
	}
    }
    g_slist_free(plist);
}

/* currently not in use anywhere */
void
hp_thread_exit(hp_t *hp)
{
    GSList *iterator = rlist;
    void *tmp;
    while(iterator) {
	tmp = iterator->data;
	iterator = iterator->next;
	hp->hp_node_destructor(tmp);
    }
    g_slist_free(rlist);
}

/* add node_ptr to my retire list */
void
retire_node(hp_t *hp, void *node_ptr)
{
    rlist = g_slist_prepend(rlist, node_ptr);
    cnt++;
    if (cnt > 20) {
	scan(hp);
    }
}




