#define number_of_items 10
#define nothing (number_of_items + 2)

int head = nothing;
int tail = nothing;

typedef item {
  int next;
  int data;
};

item memory[nothing + 1];

int enqueued = 0;
int dequeued = 0;

int dequeued_prev_prev = -2;
int dequeued_prev = -1;

init {
  int i;
  for (i : 0 .. number_of_items - 1) {
    memory[i].next = nothing;
    memory[i].data = i;
  }
  atomic {
    run produce();
    run consume()
  }
}

byte producer = 0;
byte consumer = 1;

bool wants_to_enter[2];
byte turn = producer;

inline enter_critical_section(caller) {
#ifdef ENABLE_CRITICAL_SECTION
  byte other;
  if
  :: caller == producer -> other = consumer
  :: caller == consumer -> other = producer
  fi

  wants_to_enter[caller] = true;
  turn = other;
  !wants_to_enter[other] || (turn == caller);
#else
  skip
#endif
}

inline leave_critical_section(caller) {
#ifdef ENABLE_CRITICAL_SECTION
  wants_to_enter[caller] = false;
#else
  skip
#endif
}

inline enqueue(address) {
  if 
  :: tail != nothing -> 
    memory[tail].next = address; 
  :: else
  fi;

  tail = address;

  if 
  :: head == nothing -> head = address;
  :: else
  fi
}

bool producer_finished = false;

proctype produce() {
  do
  :: enqueued < number_of_items -> 
    enter_critical_section(producer);
    enqueue(enqueued);
    leave_critical_section(producer);
    
    printf("enqueued: %d\n", memory[enqueued].data);

    enqueued++

  :: else -> 
    producer_finished = true;
    printf("produce finished\n");
    break
  od
}


inline dequeue(address) {
  address = head;

  head = memory[address].next;

  if 
  :: head == nothing -> tail = nothing
  :: else
  fi
}


#define is_empty() (head == nothing)

proctype consume() {
  do
  :: is_empty() && producer_finished ->
    printf("consume finished\n");
    break

  :: !is_empty() ->
    int address;
    enter_critical_section(consumer);
    dequeue(address);
    leave_critical_section(consumer);

    atomic {
      dequeued_prev_prev = dequeued_prev;
      dequeued_prev = memory[address].data;
    }

    dequeued++;
    
    printf("dequeued: %d\n", memory[address].data)
  od
}

ltl no_item_lost { 
  eventually (dequeued == number_of_items)
}

ltl order_preserved {
  always (dequeued_prev == dequeued_prev_prev + 1)
}