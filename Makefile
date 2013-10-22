DEBUGGING := -g -O0

CC          := gcc -std=c99
CFLAGS      := -O0 -DINTEL -DCACHE_LINE_SIZE=`getconf LEVEL1_DCACHE_LINESIZE`
LDFLAGS     := -lpthread `pkg-config --libs glib-2.0 gsl`

CFLAGS      += $(DEBUGGING)
#CFLAGS       += -DNDEBUG

COMMON_DEPS += Makefile $(wildcard *.h)

TARGETS    := perf_meas unittests

all: $(TARGETS)

clean:
	rm -f $(TARGETS) *~ core *.o *.a


%.o: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

unittests: %: %.o prioq.o ptst.o gc.o j_util.o
	$(CC) -o $@ $^ $(LDFLAGS)

perf_meas: %: %.o prioq.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

