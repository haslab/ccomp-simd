.PHONY : clean

run-all: all
	./main-gcc
	./main-ccomp

all: main-gcc main-ccomp

main-gcc: main.c encrypt.c
	gcc -m32 -Wall -O2 -maes -msse4.1 -c encrypt.c
	gcc -m32 -Wall -O2 -maes -msse4.1 -o main-gcc main.c encrypt.o

main-ccomp: main.c encrypt.c
	./../../../ccomp -mmmx -maes -msse4.1 -D__SSE4_1__ -S encrypt.c -I../ccomp-include/
	./../../../ccomp -o main-ccomp main.c encrypt.s

# global aez
main-aez: aez.c
	./../../../ccomp -mmmx -maes -msse4.1 -D__SSE4_1__ -o main-aez aez.c -I../ccomp-include/

ta:
	./../../../ccomp -mmmx -maes -msse4.1 -D__SSE4_1__ -c -fta -dmir aez.c -I../ccomp-include/

clean:
	rm -f main-gcc main-ccomp main-aez
	find . -name "*.s" -exec rm {} \;
	find . -name "*.o" -exec rm {} \;
	find . -name "*~" -exec rm {} \;
