.PHONY : clean

all: main-gcc main-ccomp
run-all: all
	./main-gcc > gcc.out
	./main-ccomp > ccomp.out
	diff gcc.out ccomp.out

main-gcc: test-xor.c
	gcc -Wfatal-errors -m32 -Wall -O2 -maes -msse4.1 -o main-gcc test-xor.c

main-ccomp: test-xor.c
	ccomp -D__MMX__ -msse4.1 -I../headers/ -dmach -S test-xor.c
	ccomp -D__MMX__ -msse4.1 -I../headers/ -o main-ccomp test-xor.s

clean:
	rm -f main-gcc main-ccomp
	find . -name "*.s" -exec rm {} \;
	find . -name "*.o" -exec rm {} \;
	find . -name "*.out" -exec rm {} \;
	find . -name "*~" -exec rm {} \;
