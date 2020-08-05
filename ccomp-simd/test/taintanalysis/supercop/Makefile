ifeq ($(SIZE),)
EXTRA:=
else
EXTRA:=-DN=$(SIZE)
endif

CCOMP:=../../../ccomp -c -I . -I ../../simd/ccomp-include -mmmx -maes -msse4.1 -D__SSE4_1__ $(EXTRA)

all: crypto_aead_aezv3.ta crypto_aead_aezv4.ta

.SUFFIXES: .va .ta .mir

%.ta: %.c
	$(CCOMP) -fta $<

%.va: %.c
	$(CCOMP) -fva $< | sed -e 's/ \([0-9]\+\):/\n\1:/g' > $@

%.mir: %.c
	$(CCOMP) -dmir $<
