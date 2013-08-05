#ifndef COMMON_H
#define COMMON_H
#include <inttypes.h>




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
