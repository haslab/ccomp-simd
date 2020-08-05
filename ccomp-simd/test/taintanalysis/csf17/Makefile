CCOMP:=../../../ccomp -c

all: salsa20.ta

%.ta: %.c
	$(CCOMP) -fta $<

%.va: %.c
	$(CCOMP) -fva $< | sed -e 's/ \([0-9]\+\):/\n\1:/g' > $@

%.mir: %.c
	$(CCOMP) -dmir $<
