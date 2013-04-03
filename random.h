/******************************************************************************
 * random.h
 * 
 * A really simple random-number generator. Crappy linear congruential
 * taken from glibc, but has at least a 2^32 period.
 */

#ifndef __RANDOM_H__
#define __RANDOM_H__

typedef unsigned long rand_t;

#define rand_init(_ptst) \
    ((_ptst)->rand = RDTICK())


