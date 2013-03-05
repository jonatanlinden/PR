/*****
 * Priority queue linked list, with invariant deleted nodes to the left.
 * Directly from Martin Vechev et al., Experience with Model Checking
 * Linearizability, 2009.
 */

#define IF if ::
#define FI :: else fi

#define isset(v,n) (v >> n & 1)
inline one(v,n)
{
  v = v | (1 << n);
}
inline null(v,n)
{
  v = v & ~(1 << n);
}

#define NLEVELS 2
#define THREADS 3
#define NODES 20
#define MAX_OPS 3
#define maxOff 2

/* Operation types. */
#define INS   0
#define DEL   1

/* Return values for each operation. */
#define RET_INVALID 0
#define RET_FALSE   1
#define RET_TRUE    2

/* types */

#define idx_t byte
#define key_t byte


typedef id_t
{
  //byte val; /* encode bit array, one bit per thread */
  bit val[THREADS];
};

id_t notify[NODES];

typedef node_t {
  key_t key;
  bit level;
  /* the following 2 fields should be stored in one mem pos */
  bit del;
  idx_t next[NLEVELS];
}

typedef queue_t {
  idx_t head, tail;
}

node_t nodes[NODES];

/**********  declaration of global variables *************/


/* hacks - spin does not accept defines in for loops */
byte gthreads;
byte gmax_ops;
byte gnodes;
/* END hacks */


byte clients_finished;
queue_t q;
bit seqq[NODES];
idx_t glob_entry;



/********* sequential specification **************/

/* adding - no similar element in queue */
inline seq_add(entry, k) {
  assert(!seqq[k]);
  seqq[k] = 1;
}

/* removing - element should be the smallest */
inline seq_remove(kl) {
  assert(seqq[kl]);
  for (i : 0..kl-1) {
    assert(seqq[i] == 0);
  }
  seqq[kl] = 0;
}



/* rng */
inline pick_key(var) { 
  atomic {
  select(var : 1..5);
  }
}


inline notify_others(kl)
{
  assert(_pid < THREADS);
  assert(kl < NODES);

  atomic{
    /* notify everyone (i won't check myself, since i've just
     * linearized. */
    for (i : 0..gthreads-1) {
      notify[kl].val[i] = 1;
      //one(notify[kl].val, i);
      //notify[kl].val = notify[kl].val & (1 << _pid);
    };
  }
}

#define i_was_notified(k) notify[k].val[_pid] //isset(notify[k].val,_pid)

inline zero_my_key(k) {
  notify[k].val[_pid] = 0;
  //d_step {
  //notify[k].val = notify[k].val & ~(1 << _pid);
  //}
  //null(notify[k].val, _pid);
}

/* node should be of node_type */
inline alloc_node(idx, k)
{
  get_entry(idx);
  nodes[idx].key = k;
  select(lvl : 0..1); // ok, since called before find
  nodes[idx].level = lvl; 
}

inline find(key) {
  found = 0;
  do ::
  i = 0;
  lvl = NLEVELS - 1;
  bef = q.head;
  do
    :: aft = nodes[bef].next[lvl];
       do
	 :: key > nodes[aft].key || (lvl == 0 && nodes[bef].del && nodes[bef].next[0] == aft && aft != q.tail) ->
	    bef = aft;
	    aft = nodes[bef].next[lvl];
	 :: else -> break
       od;
       IF (nodes[bef].next[lvl] != aft) ->
	 i = 1;
	 break;
       FI;
       
       befs[lvl] = bef;
       afts[lvl] = aft;		

       if
	 :: lvl > 0 -> lvl--
	 :: else -> break
       fi
  od;
	IF (i == 0) -> break;
	FI;
  od;
  IF (nodes[aft].key == key && (!nodes[bef].del && nodes[bef].next[0] == aft)) -> found = 1;
  FI;
}


/* Let thread tid insert key key in q */
inline insert(key)
{
  printf("enter insert\n");
  /* create node */
  alloc_node(idx, key);

start:
  /* search */
  find(key);
  IF (found) ->
    retval = RET_FALSE;
    goto end_add;
  FI;

  nodes[idx].next[0] = afts[0];
  nodes[idx].next[1] = afts[1];


  
  /* swing pred pointer, if not aft is deleted */
  atomic { /*cas */ /* linearization point of non-failed op */
    if
      :: (nodes[befs[0]].del == 0 && nodes[befs[0]].next[0] == afts[0]) ->
	 nodes[befs[0]].next[0] = idx;
	 notify_others(key);
	 seq_add(idx, key);
     :: else -> goto start; /* restart */
    fi;
  }

  IF (nodes[idx].level == 0) -> retval = RET_TRUE; goto end_add;
  FI;
  /* swing upper levels */
  do :: {
    atomic { /*cas */
      IF (nodes[befs[1]].next[1] == afts[1]) ->
	nodes[befs[1]].next[1] = idx;
	break;
      FI;
      find(key); /* update befs and afts */
      IF (!found) -> retval = RET_TRUE; /* removed during insertion */
	goto end_add;
      FI;
      nodes[idx].next[1] = afts[1];
    }
  }
  od;
  /* we're done */
  retval = RET_TRUE;
  goto end_add;

end_add:
  printf("return insert\n");
}

/* Let thread tid delete smallest element in queue */
inline delete ()
{
  printf("enter delete\n");
    offset = 0;

restart:
  bef = q.head;
  obs_head = nodes[bef].next[0];
  
  /* search at bottom level */
do
  :: (nodes[bef].del == 0 && nodes[bef].next[0] != q.tail) ->  atomic {
      IF (nodes[bef].del == 0) ->
	nodes[bef].del = 1;
	key = nodes[nodes[bef].next[0]].key;
	seq_remove(key);
	notify_others(key);
	retval = RET_TRUE;
	break; /* stored in preds next pointer */
      FI;
    }
    :: else -> 
       IF (nodes[bef].next[0] == q.tail) ->
	 retval = RET_FALSE;
	 goto end_remove;
       FI;
       bef = nodes[bef].next[0];
       offset ++;
  od;
  IF (offset >= maxOff) ->
    atomic {  /* cas */
      IF(nodes[q.head].next[0] == obs_head) -> {
	nodes[q.head].next[0] = nodes[bef].next[0]; printf("hp reset.\n");
	/* TODO: here, could restructure/add to retire list. */

      }
      FI;
    }
  FI;
  retval = RET_TRUE;
  goto end_remove;

end_remove:
  printf("return delete\n");
}


inline init_globals()
{
  
  /* init the structure */
  atomic {
    glob_entry = 0;
    gthreads = THREADS;
    gmax_ops = MAX_OPS;
    gnodes = NODES;
    /* tail */
    alloc_node(idx, 7);
    q.tail = idx;
    nodes[q.tail].level = 1;

    alloc_node(idx, 0);
    q.head = idx;
    nodes[q.head].level = 1;
    for (i : 0..1) { /* levels */
      nodes[q.head].next[i] = q.tail;
    };
  }
}

inline start_op() {
  init_locals();
  zero_my_key(key);
};

inline end_op() {
  zero_my_key(key);
  key = 0;
  op = 0;
  idx = 0;
  retval = RET_INVALID;
}

inline exec_op(key) {
  start_op();
  assert(key < NODES);
  if
    :: op = INS; 
       pick_key(key);
       insert (key);
    :: op = DEL; delete();
  fi;

  assert(retval == RET_TRUE || retval == RET_FALSE);

/* Check non-fixed linearization point, i.e., when operation
 * failed. */
  
  IF (op == DEL && retval == RET_FALSE) ->
    assert(i_was_notified(key) || !seqq[key]);
  FI;
  IF (op == INS && retval == RET_FALSE) ->
    assert(i_was_notified(key) || seqq[key]);
  FI;
  end_op();
}


inline get_entry(ptr)
{
  d_step{
    ptr = glob_entry;
    assert(ptr < NODES - 1);
    glob_entry++;
  }
}


inline execute()
{
  byte _dummy1;
  for (_dummy1 : 0..gmax_ops) {
	  exec_op(key);
	}
}


inline init_locals()
{
  bef = 0;
  aft = 0;
  befs[0] = 0;
  befs[1] = 0;
  afts[0] = 0;
  afts[1] = 0;
  offset = 0;
  obs_head = 0;
  retval = RET_INVALID;
}


inline define_locals()
{
  idx_t bef, aft, obs_head, offset;
  idx_t befs[NLEVELS], afts[NLEVELS];
  byte i;
  byte retval;
  bit op;
  byte key;
  bit lvl, found;
  idx_t idx;
  init_locals();

}


proctype client() {
  define_locals();
  execute();
}

init {
  atomic{
    byte _dummy0;
    define_locals();
    init_globals();
    for ( _dummy0 : 1..gthreads - 1) {
      run client();
    }
  }
  execute();

  /* wait until the other process finishes. */
  _nr_pr == 1;

/* extra checking ? */
  bef = q.head;
  offset = 0;
  printf("%d,", nodes[bef].del);
  bef = nodes[bef].next[0];
  for (i : 0..(3*gthreads)) {
    printf("%d -> %d,", nodes[bef].key, nodes[bef].del);
    IF (bef == q.tail) ->
      break;
    FI;
IF (offset == 1) -> assert(nodes[bef].key <= nodes[nodes[bef].next[0]].key);
FI;

IF (!nodes[bef].del) -> offset = 1;
FI;
    bef = nodes[bef].next[0];
  };
  printf("\n");
}




