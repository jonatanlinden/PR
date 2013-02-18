#define _GNU_SOURCE
#include <sched.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include "j_util.h"

pid_t 
gettid(void) 
{
    return (pid_t) syscall(SYS_gettid);
}


void
pin(pid_t t, int cpu) 
{
  cpu_set_t cpuset;
  CPU_ZERO(&cpuset);
  CPU_SET(cpu, &cpuset);
  E_en(sched_setaffinity(t, sizeof(cpu_set_t), &cpuset));
}

int
getcoreid() 
{
    cpu_set_t cpuset;
    int cpu, b = 0;
    
    CPU_ZERO(&cpuset);
    E_en(sched_getaffinity(0, sizeof(cpu_set_t), &cpuset));
    
    for (int i = 0; i < CPU_SETSIZE; i++) {

	cpu = CPU_ISSET(i, &cpuset);
	if (cpu) {
	    b |= 1<<i;
	}
    }
    return b;
}

/* works on linux systems */
uint64_t 
nsec_now (void) 
{
        struct timespec ts;
        E_en(clock_gettime(CLOCK_MONOTONIC, &ts));
        return
                (uint64_t) ts.tv_sec * 1000000000ULL +
                (uint64_t) ts.tv_nsec;
}

