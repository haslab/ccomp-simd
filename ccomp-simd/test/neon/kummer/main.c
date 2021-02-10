#include <time.h>
#include "keys.h"
#include "smult.h"
#include <stdio.h>


#define CLOCK 1000000000
#define NUMBER_OF_RUNS 10000

double calculate_cpu_cycles(struct timespec start, struct timespec end);

int main() {

	struct timespec start, stop;
	double time;
	int i,j;

	unsigned char pk_temp[48];

	clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&start);
	for(i=0;i<NUMBER_OF_RUNS;i++){
		crypto_scalarmult_base(pk_temp,sks[0]);
	}
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&stop);

	time = calculate_cpu_cycles(start, stop);

	// Check results
	i = 1;
	for(j=0;i && j<48;j++)
	  if(pk_temp[j]!=pk0[j]) i = 0;

	if (i)
	  printf("Result OK.\n");
	else
	  printf("Result NOT OK!!!\n");

	printf("cycles: %f\n",time);

	return 0;
}

double calculate_cpu_cycles(struct timespec start, struct timespec end) {
	struct timespec temp;
	double time, sec, nsec;

	if ((end.tv_nsec - start.tv_nsec) < 0) {
		temp.tv_sec = end.tv_sec - start.tv_sec - 1;
		temp.tv_nsec = 1000000000 + end.tv_nsec - start.tv_nsec;
	} else {
		temp.tv_sec = end.tv_sec - start.tv_sec;
		temp.tv_nsec = end.tv_nsec - start.tv_nsec;
	}

	sec = (double) temp.tv_sec;
        nsec = (double) temp.tv_nsec;

	time = ((sec * 1000000000) + nsec) / ((double) NUMBER_OF_RUNS);

	return time;
}

