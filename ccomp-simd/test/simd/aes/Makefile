CCOMPDIR = ../../..
include $(CCOMPDIR)/Makefile.config

CCOMP = $(CCOMPDIR)/ccomp
CCOMP_CFLAGS = -stdlib ../../../runtime 

CC = gcc-4.9 -fno-PIC -Wl,-read_only_relocs -Wl,suppress -m32
#CC = gcc -g -m32
GCC_CFLAGS = -O1 -Wall
GCCO0_CFLAGS = -O0 -Wall
GCCO1_CFLAGS = -O1 -Wall
GCCO2_CFLAGS = -O2 -Wall
GCCO3_CFLAGS = -O3 -Wall

SSEFLAGS = -msse4.1 -maes

PROGS = aesref aesni-ecb aesni-cbc aesni-ctr aesni-ecb4

all: $(PROGS:%=%.compcert) all_gcc

all_s: $(PROGS:%=%.s)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.c $(CCOMP)
	$(CCOMP) $(CCOMP_CFLAGS) $(SSEFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c $(CCOMP)
	$(CCOMP) $(CCOMP_CFLAGS) $(SSEFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(GCC_CFLAGS) $(SSEFLAGS) -o $*.gcc $*.c $(LIBS)

%.gccO0: %.c
	$(CC) $(GCCO0_CFLAGS) $(SSEFLAGS) -o $*.gccO0 $*.c $(LIBS)

%.gccO1: %.c
	$(CC) $(GCCO1_CFLAGS) $(SSEFLAGS) -o $*.gccO1 $*.c $(LIBS)

%.gccO2: %.c
	$(CC) $(GCCO2_CFLAGS) $(SSEFLAGS) -o $*.gccO2 $*.c $(LIBS)

%.gccO3: %.c
	$(CC) $(GCCO3_CFLAGS) $(SSEFLAGS) -o $*.gccO3 $*.c $(LIBS)

clean:
	rm -f *.compcert *.gcc *.gccO0 *.gccO1 *.gccO2 *.gccO3
	rm -f *.compcert.c *.s *.o *~
	rm -f  *.light.c *.parsed.c *.cm *.rtl.? *.ltl *.alloctrace

NBLOCKS = 800
NREP = 10000
bench: $(PROGS:%=%.compcert) $(PROGS:%=%.gccO0)  $(PROGS:%=%.gccO1) $(PROGS:%=%.gccO2) $(PROGS:%=%.gccO3)
	 ./*.compcert 128 0 
	@for i in $(PROGS); do ./$$i.compcert 128 $(NBLOCKS) $(NREP); ./$$i.gccO0 128 $(NBLOCKS) $(NREP); ./$$i.gccO1 128 $(NBLOCKS) $(NREP); ./$$i.gccO2 128 $(NBLOCKS) $(NREP); ./$$i.gccO3 128 $(NBLOCKS) $(NREP); done
