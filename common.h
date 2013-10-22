#ifndef COMMON_H
#define COMMON_H
#define _GNU_SOURCE
#include <inttypes.h>
#include <sched.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>


#define DCACHELINE __attribute__((aligned (2*LEVEL1_DCACHE_LINESIZE)))
#define CACHELINE  __attribute__((aligned (1*LEVEL1_DCACHE_LINESIZE)))

#define ATPAGESIZE   __attribute__((aligned (PAGESIZE)))

#ifdef NDEBUG
#define dprintf(M, ...)
#else
#define dprintf(M, ...) fprintf(stderr, "[DEBUG] %s:%d: " M "\n", __FILE__, __LINE__, ##__VA_ARGS__)
#endif

#define E(c)					\
    do {					\
	int _c = (c);				\
	if (_c < 0) {				\
	    fprintf(stderr, "E: %s: %d: %s\n",	\
		    __FILE__, __LINE__, #c);	\
	}					\
    } while (0)


#define E_en(c)					\
    do {					\
	int _c = (c);				\
	if (_c < 0) {				\
	    errno = _c; perror("E_en");		\
	}					\
    } while (0)
    
#define E_0(c)					\
    do {					\
	if ((c) == NULL) {			\
	    perror("E_0");			\
	}					\
    } while (0)

#define clean_errno() (errno == 0 ? "None" : strerror(errno))

#define log_err(M, ...) fprintf(stderr, "[ERROR] (%s:%d: errno: %s) " M "\n", __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__)
  
#define log_warn(M, ...) fprintf(stderr, "[WARN] (%s:%d: errno: %s) " M "\n", __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__)

#define log_info(M, ...) fprintf(stderr, "[INFO] (%s:%d) " M "\n", __FILE__, __LINE__, ##__VA_ARGS__)

#define check_debug(A, M, ...) if(!(A)) { dprintf(M, ##__VA_ARGS__); errno=0; } 


#if defined(__x86_64__)
/* accurate time measurements on late intel cpus */
static inline uint64_t __attribute__((always_inline))
read_tsc_p()
{
   uint64_t tsc;
   __asm__ __volatile__ ("rdtscp\n"
	 "shl $32, %%rdx\n"
	 "or %%rdx, %%rax"
	 : "=a"(tsc)
	 :
	 : "%rcx", "%rdx");
   return tsc;
}

#define IMB()    __asm__ __volatile__("mfence":::"memory")
#define IRMB()   __asm__ __volatile__("lfence":::"memory")
#define IWMB()   __asm__ __volatile__("sfence":::"memory")

#else
#error Unsupported architecture
#endif // __x86_64__






// Courtesy to Keir Fraser
#define get_marked_ref(_p)      ((void *)(((unsigned long)(_p)) | 1))
#define get_unmarked_ref(_p)    ((void *)(((unsigned long)(_p)) & ~1))
#define is_marked_ref(_p)       (((unsigned long)(_p)) & 1)

#endif 
