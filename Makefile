DEBUGGING := -g -O0

CC          := gcc -std=c99
CFLAGS      := -O3 -DINTEL -DCACHE_LINE_SIZE=`getconf LEVEL1_DCACHE_LINESIZE`
LDFLAGS     := -lpthread `pkg-config --libs glib-2.0 gsl`

#CFLAGS      += $(DEBUGGING)
#CFLAGS       += -DNDEBUG

COMMON_DEPS += Makefile $(wildcard *.h)

TARGETS    := perf_meas unittests

TARGS := prioq

all: $(TARGETS)

clean:
	rm -f $(TARGETS) *~ core *.o *.a gc/*.o


$(TARGS): %: %.o set_harness.o gc/ptst.o gc/gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

%.o: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

unittests: CFLAGS += -O0 -g
unittests: %: %.o prioq.o gc/ptst.o gc/gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

perf_meas: %: %.o prioq.o gc/ptst.o gc/gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

