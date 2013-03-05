PR
==

A lock-free priority queue implementation based on Keir Fraser's skip list implementation.


### Build

    make prioq

### Usage

Run the benchmark application as:

    ./prioq 8 1000 15 64 2000
    
This will start 8 threads, simulating a PDES workload with
exponentially distributed interevent times with an intensity of
1000. The initial length of the list will be 2^15, the offset
parameter of the algorithm will be set to 64, and the threads will
perform a simulated local computation, taking about 2000 cycles,
between access to the queue (an access = deletemin followed by an
insert).

### Build Dependencies

    gsl, glib


### Extras

A SPIN model is included, with linearizability checks of the
operations.
