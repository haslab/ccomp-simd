.PHONY : clean

all: main-ccomp main-gcc

main-ccomp: main.c
	ccomp -mmmx -maes -msse4.1 -D__SSE4_1__ -S -o main-ccomp.s main.c -I../aez/ccomp-include/
	ccomp -mmmx -maes -msse4.1 -D__SSE4_1__ -o main-ccomp main.c -I../aez/ccomp-include/

main-gcc: main.c
	gcc -m32 -Wall -O1 -msse4.1 -S -o main-gcc.s main.c
	gcc -m32 -Wall -O1 -msse4.1 -o main-gcc main.c

run-all: main-ccomp main-gcc
	sde -glm -mix -omix main-ccomp.omix.out -icount -- ./main-ccomp > main-ccomp.out
	./main-gcc > main-gcc.out

clean:
	rm -f main-ccomp main-gcc
	rm -f main-ccomp.omix.out main-ccomp.out
	find -name "*~" -exec rm {} \;
	find -name "*.s" -exec rm {} \;
	find -name "*.o" -exec rm {} \;
	find -name "*sde-icount*" -exec rm {} \;

