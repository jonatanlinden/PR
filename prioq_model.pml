/*****
 * Verification of the linearizability of the priority queue algorithm
 * presented in the paper, and that the algorithm implements a priority
 * queue.
 *
 * Some optimizations can be done, like reusing variables, replacing
 * the CAS macros, changing
 * some types from byte to bit (i.e. if limiting the number of levels
 * to two). We've omitted them here for the sake of clarity.
 *
 * Adapted from Martin Vechev et al., Experience with Model Checking
 * Linearizability, 2009.
 */

#define IF if ::
#define FI :: else fi

#define CAS(a,o,n) \
    cas_success = 0;   \
    if :: (a == o) -> a = n; cas_success = 1; \
       :: else fi

#define CASD(a, d, o, n) \
    cas_success = 0;     \
    if :: (d == 0 && a == o) -> a = n; cas_success = 1; \
    :: else fi

#define GCASSERT(new, old) \
    assert(nodes[new].recycled == 0 || nodes[old].recycled);

#define NLEVELS 2 /* 2 level skiplist */
#define THREADS 2 /* 2 threads */
#define NODES 11  /* total memory */
#define MAX_OPS 3 /* no. of random ops per thread */
#define BOUNDOFFSET 2 /* restructure offset */

/* Operation types. */
#define INS   0
#define DEL   1

/* types */
#define key_t byte
#define idx_t byte

typedef node_t {
  key_t key;
  bit level;
  bit inserting;
  bit recycled;
  /* the following 2 fields are colocated in one mem pos,
   * and should be treated as such. */
  bit d;
  idx_t next[NLEVELS];
}

typedef queue_t {
  idx_t head, tail;
}

/* this is the memory */
node_t nodes[NODES];

/**********  declaration of global variables *************/


queue_t q; /* the priority queue */
byte seqq[NODES]; /* the sequential spec. */
idx_t glob_entry; /* pointer to free memory */

/********* sequential specification **************/

/* adding */
inline seq_add(entry, k) {
  assert(seqq[k] == 0);
  seqq[k] = 1;
}

/* removing - element should be the smallest */
inline seq_remove(kl) {
  assert(seqq[kl]);
    for (j : 0..kl-1) {
    assert(seqq[j] == 0);
  }
  seqq[kl] = seqq[kl] - 1;
}
/* if empty, no entry in queue */
inline seq_empty() {
  for (j : 0..(NODES-1)) {
    assert(seqq[j] == 0);
  }
}

/************* Handling nodes/memory *****************/

inline get_entry(ptr)
{
  d_step{
    ptr = glob_entry;
    assert(ptr < NODES - 1);
    glob_entry++;
  }
}


/* return index pointing to a node being free to use */
inline alloc_node(new, k)
{
  atomic {
    get_entry(new);
    nodes[new].key = k;
    select(i : 0..(NLEVELS - 1)); /* ok, since called before locatepreds */
    nodes[new].level = i;
    nodes[new].inserting = 1;
  }
}


/*******************************************************************
 * BEGIN PRIORITY QUEUE ALGORITHM
 *******************************************************************/


inline LocatePreds(key) {

  d_step { /* local vars */
    i = NLEVELS - 1;
    pred = q.head;
    obs_head = 0;
  }
  do :: /* while i >= 0 */
	d_step { /* colocated together */
	  cur = nodes[pred].next[i];
	  d = nodes[pred].d;
	}
	do
	  :: (nodes[cur].key < key || nodes[cur].d ||
	      (i == 0 && d))  ->
	     atomic {
	       IF (i == 0/* FIX nlevels -1 */ && cur == succs[i+1]) ->
		 obs_head = 1;
	       FI;
	       pred = cur; /* local */
	      cur = nodes[pred].next[i]; /* colocated together */
	      d = nodes[pred].d;
	    }
	 :: else -> break
       od;
       atomic { /* local vars */
	 preds[i] = pred;
	 succs[i] = cur;
	 IF(i == 0) -> break FI;
	 i = 0;
       }
  od;
}

inline Restructure() {
  cur = nodes[q.head].next[i];
  i = NLEVELS - 1;
  do
    :: (i == 0) -> break;
    :: (i > 0) ->
       h = nodes[q.head].next[i];
       if :: (cur == q.tail) -> i--
	  :: else ->
	     do
	       ::
		  IF (!nodes[cur].d) -> break FI;
		  cur = nodes[cur].next[i];
	     od;
	     atomic {
	       CAS(nodes[q.head].next[i], h, cur);
	       /* descend if CAS was successful, otherwise retry */
	       IF (cas_success) ->
		 GCASSERT(cur, q.head)
		 i--
	       FI;
	     }

       fi;
  od;
}

/* Inserts key key in q */
inline Insert(key)
{
  /* create node */
  alloc_node(new, key);

start:
  /* search */
  LocatePreds(key);

  IF (nodes[succs[0]].key == key) -> goto end_insert FI;
  
  nodes[new].next[0] = succs[0];

  /* swing pred pointer, if not cur is deleted */
  atomic { /*cas */ /* linearization point of non-failed insert */
    CASD(nodes[preds[0]].next[0], nodes[preds[0]].d, succs[0], new);

    if :: (cas_success) ->
	  seq_add(new, key);
	  GCASSERT(succs[0], new);
       :: else -> goto start; /* restart */
    fi;
  }

  IF ((nodes[new].level == 0) || obs_head) -> goto end_insert FI;

  /* swing upper levels */
  j = 1;
  do :: (j == NLEVELS) -> break;
     :: (j < NLEVELS) -> 
	nodes[new].next[j] = succs[j];
	IF (nodes[new].d) -> goto end_insert FI;
	atomic { /*cas */
	  CAS(nodes[preds[j]].next[j], succs[j], new);
	  /* FIX only assert if successful */
	  IF (cas_success) ->
	    GCASSERT(succs[j], new)
	    j++
	  FI;
	}
	IF (!cas_success) ->
	  LocatePreds(key) /* update preds and succs */
	  /*IF (obs_head || nodes[succs[0]].key != key) -> goto end_insert FI;*/
	  /* something has changed, abort */
	  IF (obs_head || succs[0] != new) -> goto end_insert FI;
	  nodes[new].next[j] = succs[j]
	FI
  od;

  /* we're done */
  goto end_insert;

end_insert:
  nodes[new].inserting = 0
}

/* Delete smallest element in queue */
inline DeleteMin ()
{

  d_step {
    pred = q.head;
    obs_head = nodes[pred].next[0];
  }  
  /* walk at bottom level */
  do ::
	atomic {
	  cur = nodes[pred].next[0];
	  d   = nodes[pred].d;
	  IF (cur == q.tail) -> /* gets linearized when reading cur */
	    /* implies del bit not set */
	    seq_empty();
	    goto end_remove;
	  FI;
	}
	atomic {
	  IF (newhead == NODES && nodes[cur].inserting) -> newhead = cur;
	  FI; /* inside atomic, since only local */
	  /* del stored in preds next pointer */
	  CAS(nodes[pred].d, 0, 1);
	  if :: (cas_success) ->
		key = nodes[nodes[pred].next[0]].key;
		seq_remove(key);
		break;
	     :: else ->
		/* new pred is returned atomically by cas */
		pred = nodes[pred].next[0];
		offset ++;
	  fi;
	}
  od;
  IF (newhead == NODES) -> newhead = nodes[pred].next[0];
  FI;
  IF (offset >= BOUNDOFFSET) ->
    atomic {  /* the delete bits are both already set, only update pointer */
      CAS(nodes[q.head].next[0],obs_head,newhead);
      if :: (cas_success) -> GCASSERT(newhead, q.head)
	 :: else -> goto end_remove
      fi;
    }
    Restructure();
    do
      :: cur = obs_head;
	 IF (cur == newhead) -> break FI;
	 nodes[obs_head].recycled = 1;
	 obs_head = nodes[cur].next[0];
    od;
  FI;
  goto end_remove;

end_remove:
}


/*******************************************************************
 * END ALGORITHM
 *******************************************************************/

/* random key generator.  */
inline pick_key(var) { 
  atomic {
  select(var : 1..5);
  }
}


inline start_op() {
  init_locals();
};

inline end_op() {
  d_step {
  key = 0;
  op = 0;
  new = 0;
  }
}

inline exec_op(key) {
  start_op();
  assert(key < NODES);
  if
    :: op = INS;
       pick_key(key);
       Insert (key);
    :: op = DEL; DeleteMin();
  fi;

  end_op();
}


inline execute()
{
  byte _dummy1;
  for (_dummy1 : 0..(MAX_OPS)) {
	  exec_op(key);
  }
}

inline init_locals()
{
  d_step {
    pred = 0;
    cur = 0;
    d = 0;
    preds[0] = 0;
    preds[1] = 0;
    succs[0] = 0;
    succs[1] = 0;
    offset = 0;
    obs_head = 0;
    cas_success = 0;
    h = 0;
    i = 0;
    j = 0;
    new = 0;
    key = 0;
    newhead = NODES;
  }
}

inline define_locals()
{
  idx_t pred, cur, obs_head, offset, newhead, h;
  idx_t preds[NLEVELS], succs[NLEVELS];
  byte i,j;
  bit op, d, cas_success;
  byte key;
  
  idx_t new;
  init_locals();
}


proctype client() {
  define_locals();
  execute();
}


inline init_globals()
{
  /* init the structure */
  atomic {
    glob_entry = 0;
    /* tail */
    alloc_node(new, 7);
    q.tail = new;
    nodes[q.tail].level = 1;
    nodes[q.tail].inserting = 0;

    alloc_node(new, 0);
    q.head = new;
    nodes[q.head].level = 1;
    nodes[q.head].inserting = 0;
    for (j : 0..1) { /* levels */
      nodes[q.head].next[j] = q.tail;
    };
  }
}


init {
  atomic{
    byte _dummy0;
    define_locals();
    init_globals();
for ( _dummy0 : 1..(THREADS - 1)) {
      run client();
    }
  }
  execute();

  /* wait until the other process finishes. */
  _nr_pr == 1;

}
