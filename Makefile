DEBUGGING := -g -O0
CC	:= gcc -std=c99
CFLAGS	:= -O3 -DINTEL 
LDFLAGS	:= -lpthread `pkg-config --libs glib-2.0 gsl`

#CFLAGS      += $(DEBUGGING)
#CFLAGS       += -DNDEBUG

OS	:= $(shell uname -s)
    ifeq ($(OS),Linux)
	CFLAGS += -DCACHE_LINE_SIZE=`getconf LEVEL1_DCACHE_LINESIZE`
        LDFLAGS += -lrt
    endif
    ifeq ($(OS),Darwin)
	CFLAGS += -DCACHE_LINE_SIZE=`sysctl -n hw.cachelinesize`
    endif

OBJ_DIR = obj
objs:=$(patsubst %.c,$(OBJ_DIR)/%.o,$(wildcard *.c))

COMMON_DEPS += Makefile $(wildcard *.h)

TARGETS    := perf_meas unittests

all: $(TARGETS)

clean:
	rm -f $(TARGETS) *~ core *.o *.a gc/*.o

%.o: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

$(TARGETS): %: %.o prioq.o gc/ptst.o gc/gc.o common.o
	$(CC) -o $@ $^ $(LDFLAGS)

