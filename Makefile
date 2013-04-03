DEBUGGING := -g -O0

CC          := gcc-4.8 -std=c99
CFLAGS      := -O3 -DINTEL -fomit-frame-pointer
LDFLAGS     := -lpthread `pkg-config --libs glib-2.0 gsl`

CFLAGS      += $(DEBUGGING)
#CFLAGS       += -DNDEBUG

COMMON_DEPS += Makefile $(wildcard *.h)

GC_HARNESS_TARGETS := skip_cas prioq

TARGETS    := $(GC_HARNESS_TARGETS)

all: $(TARGETS) replay

clean:
	rm -f $(TARGETS) replay *~ core *.o *.a

replay: %: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $(patsubst %.c,%.o,$<) $<
	$(CC) -o $@ $(patsubst %.c,%.o,$<) $(LDFLAGS)


%.o: %.c $(COMMON_DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

$(GC_HARNESS_TARGETS): %: %.o set_harness.o ptst.o gc.o
	$(CC) -o $@ $^ $(LDFLAGS)

microtest: prioq.o ptst.o gc.o

tsigas: LDFLAGS += -L${HOME}/NobleDemo64/Lib/Linux64_x86 -lNOBLEDEMO64
tsigas: CFLAGS += -I${HOME}/NobleDemo64/Include
tsigas: tsigas.o set_harness.o
	$(CC) -o $@ $^ $(LDFLAGS)
