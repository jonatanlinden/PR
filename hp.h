#ifndef HP_H
#define HP_H

/* hazard pointer record, collection of one threads hazard pointers */
typedef struct hp_rec_s
{
    void **node;
    void *peek;
} hp_rec_t;

/* global storage of all hps */
typedef struct hp_s 
{
    hp_rec_t *recs;
    int nthreads;
    int K;
    uint cnt;
    void (* hp_node_destructor)(void *);

} hp_t;

typedef struct hp_ti_s
{
    void **rlist;
    int rcnt;
} hp_ti_t;


extern void retire_node(hp_t *hp, void *node_ptr);
extern hp_t *hp_init(int const K, int const nthreads, void (* hp_node_destructor)(void *));
extern void hp_destroy(hp_t *h);

#endif //HP_H
