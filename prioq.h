typedef unsigned long pkey_t;
#define KEY_NULL 0
typedef void         *val_t;

#define NUM_LEVELS 32

/* Internal key values with special meanings. */
#define SENTINEL_KEYMIN ( 0UL) /* Key value of first dummy node. */
#define SENTINEL_KEYMAX (~1UL) /* Key value of last dummy node.  */


typedef struct node_s
{
    int       level;
    val_t     v;
    int       inserting; //char pad2[4];
    pkey_t     k;
    struct node_s *next[1];
} node_t;

typedef struct
{
    int max_offset;
    int max_level;
    int nthreads;
    node_t *head;
    node_t *tail;
    char pad[64];
} pq_t;


/* Interface */

extern pq_t *pq_init(int max_offset);

extern void insert(pq_t *pq, pkey_t k, val_t v);

extern pkey_t deletemin(pq_t *pq);

extern void sequential_length(pq_t *pq);



