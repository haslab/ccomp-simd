#include <stdio.h>
#include "myneon.h"

// xyzt3  :: gfex4 xyzt3;
// xyzt2  :: gfex4 xyzt2;
// _1xyz  :: gfex4 _1xyz;
// c      :: static unsigned char __attribute__((aligned(32))) c[32];
// n      :: const unsigned char *n; // prob. 48
// _const :: static unsigned char __attribute__((aligned(32))) _const[96];

//  loop(&xyzt3,&xyzt2,&_1xyz,c,n,&_const[0]);


static const unsigned char __attribute__((aligned(32))) _28[16]       = {0xf8,0xff,0xff,0x0f,0xf8,0xff,0xff,0x0f,0xf8,0xff,0xff,0x0f,0xf8,0xff,0xff,0x0f};
static const unsigned char __attribute__((aligned(32))) _2928[16]     = {0xf8,0xff,0xff,0x1f,0xf8,0xff,0xff,0x1f,0xf8,0xff,0xff,0x0f,0xf8,0xff,0xff,0x0f};
static const unsigned char __attribute__((aligned(32))) _27[16]       = {0xfc,0xff,0xff,0x07,0xfc,0xff,0xff,0x07,0xfc,0xff,0xff,0x07,0xfc,0xff,0xff,0x07};
static const unsigned char __attribute__((aligned(32))) _28272827[16] = {0xfc,0xff,0xff,0x0f,0xfc,0xff,0xff,0x07,0xfc,0xff,0xff,0x0f,0xfc,0xff,0xff,0x07};
static const unsigned char __attribute__((aligned(32))) _mask25[16]   = {0xff,0xff,0xff,0x01,0x00,0x00,0x00,0x00,0xff,0xff,0xff,0x01,0x00,0x00,0x00,0x00};
static const unsigned char __attribute__((aligned(32))) _mask26[16]   = {0xff,0xff,0xff,0x03,0x00,0x00,0x00,0x00,0xff,0xff,0xff,0x03,0x00,0x00,0x00,0x00};

void loop(address input_0, address input_1, address input_2, address input_3, address input_4, address input_5);

typedef struct{
  int32 __attribute__((aligned(32))) v[20]; 
  /* x20 y20 x21 y21 , x22 y22 x23 y23 , x24 y24 z34 t34 , z30 t30 z31 t31 , z32 t32 z33 t33 */
} gfex4;

int main(void)
{
	unsigned int i=0;

	gfex4 xyzt3 = { { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 } };

	gfex4 xyzt2 = { { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 } };

	gfex4 _1xyz = { { 0,1,2,3,0,1,2,3,0,1,2,3,1,1,2,3,4,0,1,2 } };

	unsigned char __attribute__((aligned(32))) c[32];
		for(i=0;i<32;i++) c[i] = 0xff - i;

	unsigned char n[48];
		n[0] = 0; n[47] = 0;
		for(i=1;i<47;i++) n[i] = 0xf9 - i;

	unsigned char __attribute__((aligned(32))) _const[96];
	  for(i=0; i<16; i++) {
		 _const[i]    = _mask25[i];
		 _const[i+16] = _mask26[i];
		 _const[i+32] = _28[i];
		 _const[i+48] = _2928[i];
		 _const[i+64] = _27[i];
		 _const[i+80] = _28272827[i];
	  }

	loop((address)&xyzt3,(address)&xyzt2,(address)&_1xyz,(address)c,(address)n,(address)&_const[0]);

	for(i=0;i<20;i++)
		printf("(%08x,%08x) ",xyzt3.v[i],xyzt2.v[i]);

	printf("\n");
	
	return 0;
}
