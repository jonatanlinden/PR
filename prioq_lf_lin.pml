/*****
 * Priority queue linked list, with invariant deleted nodes to the left.
 * Directly from Martin Vechev et al., Experience with Model Checking
 * Linearizability, 2009.
 */

#define IF if ::
#define FI :: else fi

#define THREADS 2
#define NODES 7
#define maxOff 2

/* Operation types. */
#define INS   1
#define DEL   2

/* Return values for each operation. */
#define RET_RESTART 0
#define RET_FALSE   1
#define RET_TRUE    2

/* types */

#define idx_t byte
#define key_t byte

typedef id_t
{
  bit val[THREADS];
};

id_t notify[NODES];

typedef node_t {
  key_t key;
  /* the following 2 fields should be stored in one mem pos */
  bit del;
  idx_t next;
}

typedef queue_t {
  idx_t tail;
  node_t nodes[NODES];
}

/**********  declaration of global variables *************/

idx_t key_idx;
key_t keys[8];

/* rng */
inline pick_key(var) { 
  d_step {
    var = keys[key_idx];
    key_idx++;
  }
}

byte clients_finished;
queue_t q;
bit seqset[NODES];
idx_t glob_entry;

inline seq_add(entry, k) {
  assert(!seqset[k]);
  seqset[k] = 1;
}

inline seq_remove(kl) {
  if :: (seqset[kl] == 1) -> seqset[kl] = 0
     :: else -> assert(false); fi;
}


inline notify_others(kl)
{
  assert(_pid < THREADS);
  assert(kl < NODES);

  d_step{
    i = 0;
    do
      :: {
	IF (i != _pid) -> notify[kl].val[i] = 1;
	FI;
	i++;
	IF (i == THREADS) -> break;
	FI;	
      }
    od;
  }
	  


//    :: (_pid == 0) -> notify[kl].val[1] = 1;
//    :: else -> {assert(_pid == 1); notify[kl].val[0] = 1;}
//  fi;
}


#define i_was_notified(k) notify[k].val[_pid]


inline zero_my_key(k) {
  notify[k].val[_pid] = 0;
}



/* Let thread tid insert key key, using index idx in q */
inline insert(key)
{
  printf("enter insert\n");
  /* create node */
  q.nodes[idx].key = key;

start:
  /* search */
  bef = 0;
  obs_head = bef;
  
  do
    /* fast forward to first non-deleted aft */
    :: (q.nodes[bef].del == 0 || q.nodes[bef].next == q.tail) -> break;
    :: else -> bef = q.nodes[bef].next;
  od;
  aft = q.nodes[bef].next;
  do
    :: (q.nodes[aft].key > key) -> break;
    :: else -> bef = aft;
	       aft = q.nodes[bef].next;
  od;
  q.nodes[idx].next = aft;
  
  /* swing pred pointer, if not aft is deleted */
  atomic { /*cas */
    if
      :: (q.nodes[bef].del == 0 && q.nodes[bef].next == aft) ->
	 q.nodes[bef].next = idx;
	 notify_others(key);
	 seq_add(idx, key);
     :: else -> goto start; /* restart */
    fi;
  }

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
  bef = 0;
  obs_head = q.nodes[bef].next;
  
  /* search */
do
  
  :: (q.nodes[bef].del == 0 && q.nodes[bef].next != q.tail) ->  atomic {
      IF (q.nodes[bef].del == 0) ->
	q.nodes[bef].del = 1;
	key = q.nodes[q.nodes[bef].next].key;
	seq_remove(key);
	notify_others(key);
	retval = RET_TRUE;
	break; /* stored in preds next pointer */
      FI;
    }
    :: else -> 
       IF (q.nodes[bef].next == q.tail) ->
	 retval = RET_FALSE;
	 goto end_remove;
       FI;
       bef = q.nodes[bef].next;
       offset ++;
  od;
  IF (offset >= maxOff) ->
    printf("thinking about resetting hp.\n");
    atomic {  /* cas */
      IF(q.nodes[0].next == obs_head) -> {
	q.nodes[0].next = q.nodes[bef].next; printf("hp reset.\n");
	/* here, could restructure/add to retire list. */
	/* may only add to retire list if all before have del flag set.*/
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
    keys[0] = 2;
    keys[1] = 5;
    keys[2] = 4;
    keys[3] = 3;
    keys[4] = 6;
    keys[5] = 1;
    keys[6] = 7;
    keys[7] = 9;
    key_idx = 0;
    glob_entry = 1;
    q.tail = NODES - 1;
    /* tail */
    q.nodes[q.tail].key = 7;

    /* set up initial structure */
    q.nodes[0].key = 0;
    q.nodes[0].next = q.tail;
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
}

inline exec_op(op, key) {
  bool success;

  start_op();
  assert(key < NODES);
  if :: (op == INS) ->
	get_entry();
	pick_key(key);
	insert (key);
     :: (op == DEL) -> delete();
  fi;

  assert(retval == RET_TRUE || retval == RET_FALSE);
  
  IF (op == DEL && retval == RET_FALSE) ->
    {assert(i_was_notified(key) || !seqset[key]);}
  FI;
  IF (op == INS && retval == RET_FALSE) ->
    {assert(i_was_notified(key) || seqset[key]);}
  FI;

  end_op();
}

inline pick_op()
{
  atomic {
    if
      :: op = INS
      :: op = DEL
    fi;
  }
}

inline get_entry()
{
  d_step{
    idx = glob_entry;
    glob_entry++;
  }
}


inline execute()
{
  byte max_ops = 3;
  do ::
	{
	  pick_op();
	  exec_op(op, key);
	  printf("returned\n");
         if
	 :: max_ops > 1 -> max_ops--;
	 :: else -> break
       fi
	}
  od;

}


inline init_locals()
{
  bef = 0;
  aft = 0;
  offset = 0;
  obs_head = 0;
  retval = RET_RESTART;
}


inline define_locals()
{
  idx_t bef, aft, obs_head, offset;
  byte retval;
  byte op;
  byte key;
  byte i;
  idx_t idx;
  init_locals();

}


proctype client() {

  define_locals();
  execute();

  atomic {
    clients_finished++;
  };
  
}



init {
  define_locals();
  
  init_globals();
  
  run client();

  execute();

  /* wait until the other process finishes. */
  clients_finished == THREADS - 1;


}
