#ifndef J_UTIL_H
#define J_UTIL_H

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

#define FAAmodk(_addr, _x, _k)\
    ({ __typeof__(_x) _y;\
	_y = __sync_fetch_and_add((_addr), (_x)%(_k));  \
	if (_y >= 0) __sync_fetch_and_add((_addr), -(_k));  \
	_y % _k;\
    })


#define min(a,b) \
    ({ __typeof__ (a) _a = (a);	 \
	__typeof__ (b) _b = (b); \
	_a < _b ? _a : _b;	 \
    })

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

static inline void __attribute__((always_inline))
asm_atomic_inc_int32(int32_t *var)
{
    __asm__ ("lock incl %0;"
	     : "+m" (*var));
}

static inline void __attribute__((always_inline))
asm_atomic_dec_int32(int32_t *var)
{
    __asm__ ("lock decl %0;"
	     : "+m" (*var));
}

static inline int32_t __attribute__((always_inline))
asm_atomic_cmpxchg_int32(int32_t *var, int32_t old, int32_t new) {
    int32_t ret;
    /* cmpxchg uses eax as an implicit operand */
    __asm__ ("lock cmpxchgl %3, %0;"
	     : "+m" (*var), "=a" (ret)
	     : "a" (old), "r" (new));

    return ret;
}

static inline uint64_t __attribute__((always_inline))
asm_xchg (uint64_t *addr, uint64_t val)
{
    __asm__ __volatile__("lock xchg %0, %1;"
			 : "+m" (*addr), "+r" (val)
			 :: "memory", "cc");

    return val;
}



#else
#error Unsupported architecture
#endif // __x86_64__

extern pid_t gettid (void);
extern int getcoreid (void);
extern uint64_t nsec_now (void);
extern void pin (pid_t t, int cpu);

#endif // J_UTIL_H


