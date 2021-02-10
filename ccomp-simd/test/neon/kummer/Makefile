GCC=arm-linux-gnueabihf-gcc -mfloat-abi=hard -mfpu=neon -mcpu=cortex-a8
GCC_OPT= -O1
COMPCERT=../../../ccomp -stdlib ../../../runtime -fstruct-return 
CCOMP = $(COMPCERT)

SOURCES = main.c gfex2.c gfex4.c smult4.c cswap.c gfex2_mul.c
SOURCES += invert.c loop.c mul.c

OBJECTS_CCOMP = $(SOURCES:.c=.ccomp.o)
OBJECTS_GCC = $(SOURCES:.c=.gcc.o)

ASM_CCOMP = $(SOURCES:.c=.ccomp.s)
ASM_GCC = $(SOURCES:.c=.gcc.s)

all: 

all_ccomp_obj: $(OBJECTS_CCOMP)
all_gcc_obj: $(OBJECTS_GCC)

all_ccomp_s: $(ASM_CCOMP)
all_gcc_s: $(ASM_GCC)

kummer-gcc: $(SOURCES)
	$(GCC) $(GCC_OPT) -fomit-frame-pointer -fPIC -o $@ $(SOURCES)

kummer-gcc0: override GCC_OPT = -O0
kummer-gcc0: kummer-gcc

kummer-gcc1: override GCC_OPT = -O1
kummer-gcc1: kummer-gcc

kummer-gcc2: override GCC_OPT = -O2
kummer-gcc2: kummer-gcc

kummer-gcc3: override GCC_OPT = -O3
kummer-gcc3: kummer-gcc

kummer-ccomp: 
	$(CCOMP) -o $@ $(SOURCES)

%.ccomp.s: %.c
	@echo
	@echo "Generating assembly for $@"
	$(CCOMP) -o $@ -S $<
%.ccomp.o: %.c
	@echo
	@echo "Generating obj for $@"
	$(CCOMP) -o $@ -c $<


%.gcc.s: %.c
	@echo
	@echo "Generating assembly for $@"
	$(GCC) $(GCC_OPT) -o $@ -S $<
%.gcc.o: %.c
	@echo "Generating assembly for $@"
	$(GCC) $(GCC_OPT) -o $@ -c $<

clean:
	rm -f *~
	rm -f *.compcert.c *.light.c *.cm *.rtl.? *.ltl *.mach
	rm -f *.alloctrace *.alloc.in? *.alloc.live? *.alloc.out?

realclean: clean
	rm -f *.ccomp.?
	rm -f *.gcc.? *.gcc?.?
