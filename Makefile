
ARCH      := INTEL
DEBUGGING := -g -O0

ifeq ($(ARCH),INTEL)
CC          := gcc -std=c99
CFLAGS      := -O3 -DINTEL -fomit-frame-pointer
LDFLAGS     := -lpthread `pkg-config --libs glib-2.0 gsl` # -L${HOME}/local/lib -lsheriff
endif


CFLAGS      += $(DEBUGGING)
#CFLAGS       += -DNDEBUG
COMMON_DEPS += Makefile $(wildcard *.h)

GC_HARNESS_TARGETS := skip_lock_perlist skip_lock_pernode skip_lock_perpointer
GC_HARNESS_TARGETS += skip_cas skip_mcas prioq

GC_HARNESS_TARGETS += bst_lock_fraser bst_lock_manber bst_lock_kung
GC_HARNESS_TARGETS += bst_mcas

GC_HARNESS_TARGETS += rb_lock_concurrentwriters rb_lock_serialisedwriters
GC_HARNESS_TARGETS += rb_lock_mutex

TARGETS    := $(GC_HARNESS_TARGETS)
TARGETS    += rb_stm_fraser rb_stm_herlihy rb_stm_lock
TARGETS    += skip_stm_fraser skip_stm_herlihy skip_stm_lock

all: $(TARGETS) replay

clean:
	rm -f $(TARGETS) replay *~ core *.o *.a

replay: %: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $(patsubst %.c,%.o,$<) $<
	$(CC) -o $@ $(patsubst %.c,%.o,$<) $(LDFLAGS)

tree_mcas.o: tree_mcas.c mcas.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<
skip_lock_perpointer.o: skip_lock.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -DTINY_MTX -c -o $@ $<
skip_lock_pernode.o: skip_lock.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<
skip_lock_perlist.o: skip_lock.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -DFAT_MTX -c -o $@ $<
skip_mcas.o: skip_mcas.c mcas.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<


%.o: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

skip_stm_lock: skip_stm.o stm_lock.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)
skip_stm_fraser: skip_stm.o stm_fraser.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)
skip_stm_herlihy: skip_stm.o stm_herlihy.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

rb_stm_lock: rb_stm.o stm_lock.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)
rb_stm_fraser: rb_stm.o stm_fraser.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)
rb_stm_herlihy: rb_stm.o stm_herlihy.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

$(GC_HARNESS_TARGETS): %: %.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

microtest: prioq.o ptst.o gc.o

tsigas: LDFLAGS += -L${HOME}/NobleDemo64/Lib/Linux64_x86 -lNOBLEDEMO64
tsigas: CFLAGS += -I${HOME}/NobleDemo64/Include
tsigas: tsigas.o set_harness.o
	$(CC) -o $@ $^ $(LDFLAGS)
