PR
==

A lock-free priority queue implementation based on Keir Fraser's skip list implementation.


### Build

    make perf_meas

### Usage

Run the benchmark application as:

    ./perf_meas -n 8 -t 27 -o 64 
    
This will start a benchmark run with 8 threads, uniformly distributed
keys, initial queue length of 2^15 elements, the offset parameter of
the algorithm will be set to 64, and random operation (deletemin,
insert).


### Build Dependencies

    gsl, glib


### Extras

A SPIN model is included, with linearizability checks of the
operations.
