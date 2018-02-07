CC	:= gcc
CFLAGS	:= -O3 -DINTEL -Wall -std=c99
LDFLAGS	:= -lpthread -lm

OS	:= $(shell uname -s)
    ifeq ($(OS),Linux)
	CFLAGS  += -DCACHE_LINE_SIZE=`getconf LEVEL1_DCACHE_LINESIZE`
        LDFLAGS += -lrt
    endif
    ifeq ($(OS),Darwin)
	CFLAGS += -DCACHE_LINE_SIZE=`sysctl -n hw.cachelinesize`
    endif

VPATH	:= gc
DEPS	+= Makefile $(wildcard *.h) $(wildcard gc/*.h)

TARGETS := perf_meas unittests


all:	$(TARGETS)

clean:
	rm -f $(TARGETS) core *.o

%.o: %.c $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

perf_meas: CFLAGS+=-DNDEBUG
$(TARGETS): %: %.o ptst.o gc.o prioq.o common.o
	$(CC) -o $@ $^ $(LDFLAGS)

test: unittests
	./unittests

.PHONY: all clean test
