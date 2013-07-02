/*****
 * Priority queue linked list, with invariant deleted nodes to the left.
 * Directly from Martin Vechev et al., Experience with Model Checking
 * Linearizability, 2009.
 */

#define IF if ::
#define FI :: else fi

#define NLEVELS 2
#define THREADS 2
#define NODES 11
#define MAX_OPS 3
#define maxOff 2

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
  /* the following 2 fields should be stored in one mem pos */
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
  seqq[k] = seqq[k] + 1;
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
    select(i : 0..1); /* ok, since called before locatepreds */
    nodes[new].level = i;
    nodes[new].inserting = 1;
  }
}


/*************** The actual algorithm *******************/

inline LocatePreds(key) {

  d_step {
    i = NLEVELS - 1;
    pred = q.head;
    obs_head = 0;
  }
  do
    :: atomic {
      cur = nodes[pred].next[i];
      d = nodes[pred].d;
    }
       do
	 /* nodes[pred].d & nodes[pred].next[i] are in the same mem.pos. */
	 :: (nodes[cur].key <= key || nodes[cur].d ||
	     (i == 0 && d))  ->
	    d_step {
	      pred = cur; /* local */
	      cur = nodes[pred].next[i]; /* colocated together */
	      d = nodes[pred].d;
	      IF (i == 0 && cur == succs[i+1]) ->
		obs_head = 1;
	      FI;
	    }
	 :: else -> break
       od;
       atomic {
	 preds[i] = pred;
	 succs[i] = cur;		
	 if
	   :: i > 0 -> i--
	   :: else -> break
	 fi
       }
  od;
}

inline Restructure() {
  cur = q.head;
  i = NLEVELS - 1;
  do
    :: /*obs_head is used in deletemin, use pred instead */
       pred = nodes[q.head].next[i];
       do
	 ::
	    cur = nodes[cur].next[i];
	    IF (!nodes[cur].d) -> break;
	    FI;
       od;

       atomic {  /* CAS head pointer */
	 /* we don't need to check del-bit - restruct implies del */
	 IF (nodes[q.head].next[i] == pred) ->
	   nodes[q.head].next[i] = cur;
	   assert(nodes[cur].recycled == 0); /* gc */
	   break; /* WARN: assumes two-level list */
	 FI;
       }
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

  IF (succs[0] == key) -> goto end_add; FI;
  
  nodes[new].next[0] = succs[0];

  /* swing pred pointer, if not cur is deleted */
  atomic { /*cas */ /* linearization point of non-failed op */
    if
      :: (nodes[preds[0]].d == 0 && nodes[preds[0]].next[0] == succs[0]) ->
	 nodes[preds[0]].next[0] = new;
	 seq_add(new, key);
	 assert(nodes[succs[1]].recycled == 0 || nodes[new].recycled == 1) /* gc */
     :: else -> goto start; /* restart */
    fi;
  }

  IF ((nodes[new].level == 0) || obs_head) -> goto end_add; FI;

  /* swing upper levels */
  do :: {
    nodes[new].next[1] = succs[1];
    IF (nodes[new].d) -> goto end_add;
    FI;
    atomic { /*cas */
      IF (nodes[preds[1]].next[1] == succs[1]) ->
	nodes[preds[1]].next[1] = new;
	assert(nodes[succs[1]].recycled == 0 || nodes[new].recycled == 1); /* gc */
	break;
      FI;
    }
    LocatePreds(key); /* update preds and succs */
    IF (obs_head) -> goto end_add; FI;
    nodes[new].next[1] = succs[1];
  }
  od;
  /* we're done */
  goto end_add;

end_add:
  nodes[new].inserting = 0;
}

/* Delete smallest element in queue */
inline DeleteMin ()
{

  d_step{
    pred = q.head;
    obs_head = nodes[pred].next[0];
  }  
  /* walk at bottom level */
  do
    :: (nodes[pred].next[0] == q.tail) -> /* implies del bit not set */
       atomic {if :: (nodes[pred].next[0] == q.tail) ->
		     seq_empty();
		     goto end_remove;
		  :: else
	       fi;
       }
    :: (nodes[pred].next[0] != q.tail) ->
       atomic {
	 IF (newhead == NODES && nodes[pred].inserting) -> newhead = pred;
	 FI;
	 /* cas */
	 if :: (nodes[pred].d == 0) -> nodes[pred].d = 1;
	    key = nodes[nodes[pred].next[0]].key;
	    seq_remove(key);
	    break; /* stored in preds next pointer */
	 :: else ->  pred = nodes[pred].next[0]; /* this is returned
						atomically by cas */
		     offset ++;
	 fi;
       }
  od;
  IF (newhead == NODES) -> newhead = nodes[pred].next[0];
  FI;
  IF (offset >= maxOff) ->
    atomic {  /* cas */
      if :: (nodes[q.head].next[0] == obs_head) -> {
	nodes[q.head].next[0] = newhead;
	assert(nodes[newhead].recycled == 0); /* gc */
      }
	 :: else -> goto end_remove;
      fi;
    }
	 
    Restructure();
    do
      :: cur = nodes[obs_head].next[0];
	 nodes[obs_head].recycled = 1;
	 IF (cur == newhead) -> break;
	 FI;
	 obs_head = cur;
    od;
  FI;
  goto end_remove;

end_remove:
}


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
    newhead = NODES;
  }
}

inline define_locals()
{
  idx_t pred, cur, obs_head, offset;
  idx_t preds[NLEVELS], succs[NLEVELS];
  byte j, newhead;
  bit op, i, d;
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