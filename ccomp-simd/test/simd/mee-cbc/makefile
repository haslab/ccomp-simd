.PHONY: clean

CCOMP = ../../../ccomp
CCOMP_INC = -I../ccomp-include/
CCOMP_FLAGS = -mmmx -maes -msse4.1 -D__SSE4_1__ -D__SHA__

main-ccomp:
	$(CCOMP) $(CCOMP_INC) $(CCOMP_FLAGS) -o main main.c src/aes128.c src/sha256-msha.c src/decrypt_verify.c

main-gcc:
	gcc -O2 -Wall -maes -msse4.1 -msha -o main main.c src/aes128.c src/sha256-msha.c src/decrypt_verify.c

main-ccomp-run:
	sde -glm -mix -omix main.out -icount -- ./main

clean: clean-build
	rm -f main
	rm -f main.out sde-icount.txt

clean-build:
	find ./ -name "*.o" -exec rm {} \;
	find ./ -name "*~" -exec rm {} \;
	find ./ -name "*.s" -exec rm {} \;

ta:
	$(CCOMP) $(CCOMP_INC) $(CCOMP_FLAGS) -c driver.c -dmir -fta

ta_long:
	$(CCOMP) $(CCOMP_INC) $(CCOMP_FLAGS) -c all.c -dmir -fta

# disable linux yama (for more info check sde readme or the following link:
# https://www.kernel.org/doc/Documentation/security/Yama.txt) 
ubuntu-disable-yama:
	echo 0 > /proc/sys/kernel/yama/ptrace_scope

ubuntu-enable-yama:
	echo 1 > /proc/sys/kernel/yama/ptrace_scope


