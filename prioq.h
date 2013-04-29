
#include <float.h>

typedef unsigned long setkey_t;
#define SETKEY_NULL 0
//typedef double setkey_t;
typedef void         *setval_t;


#define NUM_LEVELS 20

/* Internal key values with special meanings. */
//#define INVALID_FIELD   (0)    /* Uninitialised field value.     */
#define SENTINEL_KEYMIN ( 0UL) /* Key value of first dummy node. */
#define SENTINEL_KEYMAX (~1UL) /* Key value of last dummy node.  */
#define KEY_MIN  ( 0UL)
#define KEY_MAX  (~1UL)

//#define SENTINEL_KEYMIN DBL_MIN
//#define SENTINEL_KEYMAX DBL_MAX

//#define KEYMIN DBL_MIN
//#define KEYMAX DBL_MAX



//#define END (node_t *) 0xfefefefefefefefe
#define END (node_t *) 0xc0c0c0c0c0c0c0c0



typedef struct node_s
{
    setkey_t  k;
    int       level;
    char pad2[4]; /* just to make it clear */
    setval_t  v;
    struct node_s *next[1];
} node_t;

typedef struct set_s
{
    int max_offset;
    int max_level;
    int nthreads;
    
    node_t *head;
} set_t;



extern void _init_set_subsystem(void);


/* use_this externally */

extern set_t *set_alloc(int max_offset, int max_level, int nthreads);

extern void set_update(set_t *s, setkey_t k, setval_t v);

extern setval_t set_remove(set_t *s, setkey_t k);

extern setkey_t set_removemin(set_t *s, int id);

