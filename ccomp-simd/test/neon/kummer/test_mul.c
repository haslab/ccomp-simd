#include <stdio.h>
#include "myneon.h"

typedef struct{
	unsigned int __attribute__((aligned(32))) v[20];
} gfe;

void mul(address input_0, address input_1, address input_2);

void print_gfe(char *s, gfe *g){
	int i;
	printf("%s: ",s);
	for(i=0;i<19;i++){
		printf("%4d, ",g->v[i]);
	}
	printf("%4d\n",g->v[19]);
}

int main() {

	gfe e1 = { {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19} };
	gfe e3 = { {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19} };
	gfe p1 = { {0,0,0,0,0,0,0,0,0,0,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 } };

	mul((address)&p1,(address)&e1,(address)&e3);

	print_gfe("e1",&e1);
	print_gfe("e3",&e3);
	print_gfe("p1",&p1);

	return 0;
}
