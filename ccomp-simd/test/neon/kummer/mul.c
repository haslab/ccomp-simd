#include "myneon.h"

void mul(address input_0, address input_1, address input_2) {

int128 a0;
int128 a1;
int128 a2;
int128 a3;
int128 a4;

int128 b0;
int128 b1;
int128 b2;
int128 b3;
int128 b4;

int128 _2a0;
int128 _2a1;
int128 _2a2;
int128 _2a3;
int128 _2a4;


int128 r0;
int128 r1;
int128 r2;
int128 r3;
int128 r4;

int128 r5;


int128 t;
int128 mask25;
int128 mask26;

address adr0;
address adr1;
address adr2;

int32 count;


unsigned char mask25_stack[16];
address ptr25;

/*stack128 caller_q4_stack;
stack128 caller_q5_stack;
stack128 caller_q6_stack;
stack128 caller_q7_stack;


qpushenter mul;*/

//#count = 10000;
//#loop:
//#count -= 1;
//#if (count > 0);
//#goto loop;

ptr25 = mask25_stack;

set2x(mask25,0xffffffff);
shiftl4x_in(mask25,7);
shiftur2x_in(mask25,7);

set2x(mask26,0xffffffff);
shiftl4x_in(mask26,6);
shiftur2x_in(mask26,6);

store128((mem128)ptr25,mask25);

//####;


adr1 = input_1;
load128(a0,(mem128)adr1); adr1+=16;
load128(a1,(mem128)adr1); adr1+=16;
load128(a2,(mem128)adr1); adr1+=16;

shiftl2x(_2a0,a0,1);
shiftl2x(_2a1,a1,1);
shiftl2x(_2a2,a2,1);


adr2 = input_2;
load128(b0,(mem128)adr2); adr2+=16;
load128(b1,(mem128)adr2); adr2+=16;
load128(b2,(mem128)adr2); adr2+=16;


//## First half; //##;

mul2x32_0101(r0,a0,b0)		;//#   a0 b0;
mul2x32_2301(r1,a0,b0)		;//#   a1 b0;
mul2x32_0101(r2,a1,b0)		;//#   a2 b0;
mul2x32_2301(r3,a1,b0)		;//#   a3 b0;
mul2x32_0101(r4,a2,b0)		;//#   a4 b0;

mul2x32_0123_ac(r0,_2a2,b0)		;//# 2 a4 b1;
mul2x32_0123_ac(r1,a0,b0)		;//#   a0 b1;
mul2x32_2323_ac(r2,_2a0,b0)		;//# 2 a1 b1;
mul2x32_0123_ac(r3,a1,b0)		;//#   a2 b1;
mul2x32_2323_ac(r4,_2a1,b0)		;//# 2 a3 b1;

mul2x32_2301_ac(r0,_2a1,b1)		;//# 2 a3 b2;
mul2x32_0101_ac(r1,a2,b1)		;//#   a4 b2;
mul2x32_0101_ac(r2,a0,b1)		;//#   a0 b2;
mul2x32_2301_ac(r3,a0,b1)		;//#   a1 b2;
mul2x32_0101_ac(r4,a1,b1)		;//#   a2 b2;

mul2x32_0123_ac(r0,_2a1,b1)		;//# 2 a2 b3;
mul2x32_2323_ac(r1,_2a1,b1)		;//# 2 a3 b3;
mul2x32_0123_ac(r2,_2a2,b1)		;//# 2 a4 b3;
mul2x32_0123_ac(r3,a0,b1)		;//#   a0 b3;
mul2x32_2323_ac(r4,_2a0,b1)		;//# 2 a1 b3;

mul2x32_2301_ac(r0,_2a0,b2)		;//# 2 a1 b4;
mul2x32_0101_ac(r1,a1,b2)		;//#   a2 b4;
mul2x32_2301_ac(r2,_2a1,b2)		;//# 2 a3 b4;
mul2x32_0101_ac(r3,a2,b2)		;//#   a4 b4;
mul2x32_0101_ac(r4,a0,b2)		;//#   a0 b4;


//# carry; //#;

shiftur2x(t,r0,26);
add2x(r1,r1,t);
r0 = vandq_u8(r0, mask26);

shiftur2x(t,r1,25);
add2x(r2,r2,t);
r1 = vandq_u8(r1, mask25);

shiftur2x(t,r2,26);
add2x(r3,r3,t);
r2 = vandq_u8(r2, mask26);

shiftur2x(t,r3,25);
add2x(r4,r4,t);
r3 = vandq_u8(r3, mask25);

shiftur2x(t,r4,25);
add2x(r0,r0,t);
r4 = vandq_u8(r4, mask25);
//#--;
shiftur2x(t,r0,26);
add2x(r1,r1,t);
r0 = vandq_u8(r0, mask26);


//# arrange; //#;

mix32_00100212_01110313(r0,r1);
permute32_0213(r0);
mix32_00100212_01110313(r2,r3);
permute32_0213(r2);


adr0 = input_0;
store128((mem128)adr0,r0); adr0+=16;
store128((mem128)adr0,r2); adr0+=16;

//####;


//## Second half; //##;

load128(a3,(mem128)adr1); adr1+=16;
load128(a4,(mem128)adr1); adr1+=16;

shiftl2x(_2a3,a3,1);
shiftl2x(_2a4,a4,1);

load128(b3,(mem128)adr2); adr2+=16;
load128(b4,(mem128)adr2); adr2+=16;

mul2x32_0101(r0,a3,b3)		;//#   c0 d0;
mul2x32_2301(r1,a3,b3)		;//#   c1 d0;
mul2x32_0101(r2,a4,b3)		;//#   c2 d0;
mul2x32_2301(r3,a4,b3)		;//#   c3 d0;
mul2x32_2301(r5,a2,b3)		;//#   c4 d0;

mul2x32_2323_ac(r0,_2a2,b3)		;//# 2 c4 d1;
mul2x32_0123_ac(r1,a3,b3)		;//#   c0 d1;
mul2x32_2323_ac(r2,_2a3,b3)		;//# 2 c1 d1;
mul2x32_0123_ac(r3,a4,b3)		;//#   c2 d1;
mul2x32_2323_ac(r5,_2a4,b3)		;//# 2 c3 d1;

mul2x32_2301_ac(r0,_2a4,b4)		;//# 2 c3 d2;
mul2x32_2301_ac(r1,a2,b4)		;//#   c4 d2;
mul2x32_0101_ac(r2,a3,b4)		;//#   c0 d2;
mul2x32_2301_ac(r3,a3,b4)		;//#   c1 d2;
mul2x32_0101_ac(r5,a4,b4)		;//#   c2 d2;

mul2x32_0123_ac(r0,_2a4,b4)		;//# 2 c2 d3;
mul2x32_2323_ac(r1,_2a4,b4)		;//# 2 c3 d3;
mul2x32_2323_ac(r2,_2a2,b4)		;//# 2 c4 d3;
mul2x32_0123_ac(r3,a3,b4)		;//#   c0 d3;
mul2x32_2323_ac(r5,_2a3,b4)		;//# 2 c1 d3;

mul2x32_2323_ac(r0,_2a3,b2)		;//# 2 c1 d4;
mul2x32_0123_ac(r1,a4,b2)		;//#   c2 d4;
mul2x32_2323_ac(r2,_2a4,b2)		;//# 2 c3 d4;
mul2x32_2323_ac(r3,a2,b2)		;//#   c4 d4;
mul2x32_0123_ac(r5,a3,b2)		;//#   c0 d4;


//# carry; //#;

load128(mask25,(mem128)ptr25);

shiftur2x(t,r0,26);
add2x(r1,r1,t);
r0 = vandq_u8(r0, mask26);

shiftur2x(t,r1,25);
add2x(r2,r2,t);
r1 = vandq_u8(r1, mask25);

shiftur2x(t,r2,26);
add2x(r3,r3,t);
r2 = vandq_u8(r2, mask26);

shiftur2x(t,r3,25);
add2x(r5,r5,t);
r3 = vandq_u8(r3, mask25);

shiftur2x(t,r5,25);
add2x(r0,r0,t);
r5 = vandq_u8(r5, mask25);
//#--;
shiftur2x(t,r0,26);
add2x(r1,r1,t);
r0 = vandq_u8(r0, mask26);



//# arrange; //#;

mix32_00100212_01110313(r0,r1);
permute32_0213(r0);
mix32_00100212_01110313(r2,r3);
permute32_0213(r2);

mix32_00100212_01110313(r4,r5);
permute32_0213(r4);

//####;



store128((mem128)adr0,r4); adr0+=16;
store128((mem128)adr0,r0); adr0+=16;
store128((mem128)adr0,r2); adr0+=16;


//qpopreturn;
}
