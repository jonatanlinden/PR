CC	:= gcc 
CFLAGS	:= -O0 -g -DINTEL -Wall -std=c99 `pkg-config --cflags --libs glib-2.0 gsl`
LDFLAGS	:= -lpthread `pkg-config --libs gsl glib-2.0`

OS	:= $(shell uname -s)
    ifeq ($(OS),Linux)
	CFLAGS  += -DCACHE_LINE_SIZE=`getconf LEVEL1_DCACHE_LINESIZE`
        LDFLAGS += -lrt
    endif
    ifeq ($(OS),Darwin)
	CFLAGS += -DCACHE_LINE_SIZE=`sysctl -n hw.cachelinesize`
    endif

#VPATH	:= gc
DEPS	+= Makefile $(wildcard *.h)
TARGETS := perf_meas

all: 	$(TARGETS)

clean:
	rm -f $(TARGETS) core *.o 

%.o: %.c $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

$(TARGETS): %: %.o prioq.o common.o hp.o
	$(CC) -o $@ $^ $(LDFLAGS)


.PHONY: all clean
