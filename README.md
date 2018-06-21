A Lock-Free Skiplist-Based Priority Queue
==
[![License](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://github.com/jonatanlinden/PR/blob/master/COPYING)
[![Build Status](https://travis-ci.org/jonatanlinden/PR.png?branch=master)](https://travis-ci.org/jonatanlinden/PR)


A linearizable skiplist-based lock-free priority queue implementation
minimizing the number of required CAS-instructions per operation. The
skiplist implementation is adapted from Keir Fraser's skiplist
(http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-579.pdf).

For more information about the priority queue, see
http://user.it.uu.se/~jonli208/priorityqueue.


### Build

    make perf_meas

### Usage

Run the benchmark application as:

    ./perf_meas -n 8 -o 64 -t 42 
    
This will start a benchmark run with 8 threads, the offset parameter
of the algorithm will be set to 64, and the benchmark will run for 42
seconds. Per default, the inserted keys are uniformly distributed,
operations (deletemin, insert) are randomly selected (50%/50%) and the
queue is prefilled with 2^15 elements.

Run 

    ./perf_meas -h

for more information about the available parameters.

### Extras

A model for the SPIN model checker (http://spinroot.com) is included,
with linearizability checks of the operations. The -O flag has to be
used (if SPIN version >= 6), the model is using the old scope rules.
To perform a bit state space analysis:

    spin -O -a prioq_model.pml
    gcc -O2 -DMEMLIM=2048 -DBITSTATE -o pan pan.c
    ./pan -w33


