#include "myneon.h"

void loop(address input_0, address input_1, address input_2, address input_3, address input_4, address input_5) {

  address adr0, adr1, adr2, adr3, adr4, adr5;
  //# x3 y3 z3 t3;
  //# x2 y2 z2 t2;
  //#  1  x  y  z;
  //# stepconst (128) , hadstepconst (128);

  int32 count, idx, shf, bit, swap, prevbit;
  int128 c, sum0, sum1, dif0, dif1, neg1, neg2, copy;
  int128 suma0, difa0, suma1, difa1;
  int128 rst0, rst1, rst2, rst3, rst4;
  int128 a0, a1, a2, a3, a4;
  int128 _2a0, _2a1, _2a2, _2a3, _2a4;
  int128 b0, b1, b2, b3, b4;
  int128 _2b0, _2b1, _2b2, _2b3, _2b4;
  int128 c0;
  int128 h0, h1, h2, h3, h4, h5;
  int128 k0, k1, k2, k3, k4, k5;
  int128 _2k0, _2k2, _2k4;
  int128 p0, p1, p2, p3, p4, p5;
  int128 q0, q1, q2, q3, q4, q5;
  int128 n0, n1, n2;
  int128 na0, na1;
  int128 t, t0, t1, t2, t3, t4;
  int128 mask25, mask26;
  int128 _27, _28, _29_28, _28_27_28_27;

  /*qpushenter loop;

    stack32 stack_r4;
    stack32 stack_r5;
    stack32 stack_r6;
    stack32 stack_r7;
    stack32 stack_r8;
    stack32 stack_r9;
    stack32 stack_r10;
    stack32 stack_r11;
    stack32 stack_r12;
    stack32 stack_r14;

    stack_r4 = caller_r4;
    stack_r5 = caller_r5;
    stack_r6 = caller_r6;
    stack_r7 = caller_r7;
    stack_r8 = caller_r8;
    stack_r9 = caller_r9;
    stack_r10 = caller_r10;
    stack_r11 = caller_r11;
    stack_r12 = caller_r12;
    stack_r14 = caller_r14;*/

  //#-------------------------------;

  count = 0xff;
  prevbit = 0;
  count ^= 0x4;

 looptop:

  adr4 = input_4;
  adr1 = input_1 + 16;
  adr0 = input_1 + 64;
  idx = (count >> 5);
  shf = count & 0x1f;
  idx <<= 2;
  adr4 += idx;
  adr2 = input_1;
  adr3 = input_1 + 48;
  bit = *(int32*)adr4;

  bit >>= shf	;//### latency;
  bit &= 0x1		;//### latency;
  swap = bit ^ prevbit	;//### latency;
  prevbit = bit 		;//### latency;
  bit = swap ^ 0x1;
  bit -= 1;


  //#==========;//#;
  //# Hadamard; //#;
  //#==========;//#;

  //#---------------;//#;
  //## x2 y2 z2 t2; //##;
  //## x3 y3 z3 t3; //##;
  //#---------------;//#;

  load128(b1,(mem128)adr1);
  load128(b4,(mem128)adr0)	;//# use adr0 instead of adr1;

  add4x(sum1,b1,b4);
  load128(b0,(mem128)adr2)	;//# use adr2 instead of adr1;


  adr0 = input_0 + 16;
  adr1 = input_0 + 64;
  adr2 = input_1 + 32;
  sub4x(dif1,b1,b4);
  load128(b3,(mem128)adr3)	;//# use adr3 instead of adr1;

  add4x(sum0,b0,b3);
  load128(a1,(mem128)adr0);
  sub4x(dif0,b0,b3);
  load128(a4,(mem128)adr1)	;//# use adr1 instead of adr0;

  adr0 = input_0;
  adr1 = input_0 + 32	;

  mix32_00100212_01110313(sum1,dif1)	;


  load128(b2,(mem128)adr2)	;//# use adr2 instead of adr1;

  load128(a0,(mem128)adr0);
  load128(a2,(mem128)adr1); adr1 += 16	;//# use adr1 instead of adr0;
  load128(a3,(mem128)adr1)		;//# use adr1 instead of adr0;

  add4x(suma1,a1,a4);
  swap64_00100111(sum1,b2);
  sub4x(difa1,a1,a4);
  swap64_00111001(dif1,b2);


  mix32_00100212_01110313(sum0,dif0)			;//### 1 cycle;

  add4x(b1,sum1,dif1)									;//### 1 cycle;
  mix32_00100212_01110313(suma1,difa1)	;//### 1 cycle;
  sub4x(b4,sum1,dif1)									;//### 1 cycle;

  add4x(suma0,a0,a3);
  swap64_10010011(b1,b2)	;

  add4x(b0,sum0,dif0);
  swap64_00100111(suma1,a2);

  sub4x(b3,sum0,dif0);
  swap64_00100111(b2,b4);

  adr5 = input_5;
  mix32_00010212_10110323(b1,b4);
  sub4x(difa0,a0,a3);

  adr5 += 48;
  swap64_00111001(a2,difa1);
  add4x(sum1,b1,b4);

  sub4x(dif1,b1,b4);
  load128(_29_28,(mem128)adr5);

  adr5 -= 16;

  adr0 = input_1;
  adr1 = input_1 + 48;
  adr2 = input_1 + 32;


  add4x(b0,b0,_29_28);
  load128(_28,(mem128)adr5);


  add4x(b3,b3,_29_28);
  swap64_00100111(sum1,dif1)	;//### latency;

  add4x(dif1,dif1,_28)					;//### latency;
  swap64_00100111(b2,sum1);

  add4x(b2,b2,_29_28);
  store128((mem128)adr0,b0)	;//# use adr0 instead of adr1;

  add4x(sum1,sum1,_29_28);
  store128((mem128)adr1,b3);


  adr5 = input_5;

  //#adr1 = input_1;
  //#store128((mem128)adr1,b0);
  //#adr1 = input_1 + 48;
  //#store128((mem128)adr1,b3);
  //#adr1 = input_1 + 32;
  //#store128((mem128)adr1,dif1);
  //#adr1 = input_1 + 16;
  //#store128((mem128)adr1,b2);
  //#adr1 = input_1 + 64;
  //#store128((mem128)adr1,sum1);


  adr3 = input_1 + 16;
  adr4 = input_1 + 64;



  add4x(a1,suma1,difa1);
  store128((mem128)adr2,dif1)	;//# use adr2 instead of adr1;

  sub4x(a4,suma1,difa1);
  store128((mem128)adr3,b2)	;//# use adr3 instead of adr1;

  mix32_00100212_01110313(suma0,difa0);

  store128((mem128)adr4,sum1)	;//# use adr4 instead of adr1;

  add4x(a0,suma0,difa0);
  swap64_10010011(a1,a2);

  sub4x(a3,suma0,difa0);
  swap64_00100111(a2,a4);

  mix32_00010212_10110323(a1,a4);

  adr0 = input_0 + 48;
  adr1 = input_1;

  add4x(suma1,a1,a4)		;//### latency;
  load128(mask25,(mem128)adr5); adr5+=16;

  sub4x(difa1,a1,a4);
  load128(mask26,(mem128)adr5); adr5+=16;

  load128(b0,(mem128)adr1); adr1+=16;


  swap64_00100111(a2,suma1)	;//### latency;
  add4x(a3,a3,_29_28);

  swap64_00100111(suma1,difa1);
  add4x(a0,a0,_29_28);

  add4x(a4,suma1,_29_28);


  add4x(a1,a2,_29_28);
  store128((mem128)adr0,a3); adr0+=16;

  add4x(a2,difa1,_28);
  store128((mem128)adr0,a4); adr0+=16	;//### latency;



  //##############################################################;


  //#=============;//#;
  //# First Inpu;t //#;
  //# x3 y3 z3 t3; //#;
  //#=============;//#;

  adr0 = input_1 + 48;
  load128(b1,(mem128)adr1); adr1+=16;
  load128(b3,(mem128)adr0)		;//# use adr0 instead of adr1;
  adr0 -= 16;


  //## First half; //##;

  //#---------------------------------------;//#;
  //# Multiplication;                        //#;
  //# x3 y3 z3 t3 = x3*x2 y3*y2 z3*z2 t3*t2; //#;
  //#---------------------------------------;//#;

  mul2x32_2301(h3,b1,a0);
  mul2x32_0123_ac(h3,b1,a0);

  add2x(_2b1,b1,b1);
  swap64_00100111(b0,b3);

  mul2x32_0101(h1,b1,a2);
  mul2x32_0101(h4,b1,a1);

  add2x(_2b0,b3,b3);
  load128(b2,(mem128)adr0)			;//# use adr0 instead of adr1;

  mul2x32_0101(h2,b1,a0);

  mul2x32_0101_ac(h1,b2,a1);

  add2x(_2b2,b2,b2);
  swap64_00100111(b0,b3);

  mul2x32_0101_ac(h4,b2,a0);
  mul2x32_2323_ac(h4,_2b1,a0);
  mul2x32_0123_ac(h4,_2b0,a1);
  mul2x32_0101_ac(h4,b0,a2);

  mul2x32_2301(h0,_2b1,a1);
  mul2x32_0123_ac(h0,_2b1,a1);
  mul2x32_0123_ac(h0,_2b2,a0);
  mul2x32_0101_ac(h0,b0,a0);
  mul2x32_0101_ac(h0,_2b0,a2);

  mul2x32_2323_ac(h1,_2b1,a1);
  mul2x32_2301_ac(h2,_2b1,a2);


  shiftur2x(t,h4,25);
  and128(h4, h4, mask25);

  mul2x32_2301_ac(h1,b0,a0);
  add2x(h0,h0,t);
  mul2x32_0123_ac(h1,b0,a0);

  shiftur2x(t,h0,26);
  and128(h0, h0, mask26);

  mul2x32_0123_ac(h2,_2b2,a1);
  add2x(h1,h1,t);
  mul2x32_0101_ac(h2,b0,a1);
  mul2x32_0123_ac(h2,_2b0,a0);

  shiftur2x(t,h1,25);
  and128(h1, h1, mask25);

  mul2x32_0101_ac(h3,b2,a2);
  add2x(h2,h2,t);
  mul2x32_2301_ac(h3,b0,a1);
  mul2x32_0123_ac(h3,b0,a1);


  //## serial carry && cmov; //##;

  shiftur2x(t,h2,26);
  and128(h2, h2, mask26);

  //#bit = input_4;
  xor128(t0, a0, b0);
  xor128(t1, a1, b1);
  add2x(h3,h3,t);

  //#bit -= 1;
  set4x(c,bit);

  and128(t0, t0, c);

  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  adr1 = input_1;

  xor128(b0, b0, t0);
  xor128(t2, a2, b2);
  add2x(h4,h4,t);

  and128(t1, t1, c);
  and128(t2, t2, c);
  store128((mem128)adr1,b0); adr1+=16;

  shiftur2x(t,h4,25);
  adr0 = input_0 + 48;
  load128(a3,(mem128)adr0); adr0+=16;

  and128(h4, h4, mask25);
  load128(a4,(mem128)adr0); adr0+=16;

  xor128(b1, b1, t1);
  adr1 = input_1 + 48;
  load128(b3,(mem128)adr1); adr1+=16;

  xor128(t2, t2, b2);
  mix32_00100212_01110313(h2,h3);

  add2x(h0,h0,t);
  permute32_0213(h4);

  set_lane_64_1001(b2,t2);



  //##############################################################;


  //## Second half; //##;

  //#---------------------------------------;//#;
  //# Multiplication;                        //#;
  //# x3 y3 z3 t3 = x3*x2 y3*y2 z3*z2 t3*t2; //#;
  //#---------------------------------------;//#;


  load128(b4,(mem128)adr1); adr1+=16;

  adr1 = input_1 + 16;

  add2x(_2b4,b4,b4);
  store128((mem128)adr1,b1); adr1+=16;


  mul2x32_2301(k5,b2,a3);
  set_lane_64_1001(a2,h4)	;
  mix32_00100212_01110313(h0,h1);
  mul2x32_2323_ac(k5,_2b4,a3);
  permute32_0213(h2);
  mul2x32_0101_ac(k5,b4,a4);
  permute32_0213(h0);
  store128((mem128)adr1,b2); adr1+=16;
  mul2x32_2323_ac(k5,_2b0,a4);
  mul2x32_0123_ac(k5,b3,a2);


  mul2x32_0101(k0,b3,a3);
  mul2x32_2323_ac(k0,_2b2,a3);
  mul2x32_2301_ac(k0,_2b4,a4);
  mul2x32_0123_ac(k0,_2b4,a4);
  mul2x32_2323_ac(k0,_2b0,a2);

  mul2x32_2323(k2,_2b2,a4);

  adr0 = input_0;
  shiftur2x(t,k5,25);
  store128((mem128)adr0,h0); adr0+=16;
  and128(k5, k5, mask25);
  store128((mem128)adr0,h2); adr0+=16;

  mul2x32_2301(k1,b3,a3);
  add2x(k0,k0,t);
  mul2x32_0123_ac(k1,b3,a3);
  mul2x32_2301_ac(k1,b2,a4);
  mul2x32_2323_ac(k1,_2b4,a4);
  mul2x32_0123_ac(k1,b4,a2);

  adr5 = input_5;
  adr5 += 16;
  shiftur2x(t,k0,26);
  load128(mask26,(mem128)adr5);
  and128(k0, k0, mask26);
  store128((mem128)adr0,a2); adr0+=16;

  mul2x32_0101_ac(k2,b4,a3);
  add2x(k1,k1,t);
  mul2x32_2323_ac(k2,_2b0,a3);
  mul2x32_0101_ac(k2,b3,a4);
  mul2x32_2323_ac(k2,_2b4,a2);

  shiftur2x(t,k1,25);
  and128(k1, k1, mask25);

  mul2x32_2301(k3,b4,a3);
  add2x(k2,k2,t);
  mul2x32_0123_ac(k3,b4,a3);
  mul2x32_2301_ac(k3,b3,a4);
  mul2x32_0123_ac(k3,b3,a4);
  mul2x32_2323_ac(k3,b2,a2);


  //## serial carry; //##;

  shiftur2x(t,k2,26);
  and128(k2, k2, mask26);

  //#bit = input_4;
  xor128(t3, a3, b3);
  xor128(t4, a4, b4);

  add2x(k3,k3,t);

  //#bit -= 1;
  set4x(c,bit);

  and128(t3, t3, c);

  shiftur2x(t,k3,25);
  and128(k3, k3, mask25);

  xor128(b3, b3, t3);
  xor128(t2, a2, b2);

  add2x(k5,k5,t);

  and128(t2, t2, c);
  and128(t4, t4, c);

  adr1 = input_1 + 48;
  store128((mem128)adr1,b3); adr1+=16;

  adr0 = input_0;
  shiftur2x(t,k5,25);
  load128(a0,(mem128)adr0); adr0+=16;
  and128(k5, k5, mask25);
  load128(a1,(mem128)adr0); adr0+=16;

  adr3 = input_3 + 16;
  load128(c0,(mem128)adr3);

  xor128(t2, t2, b2);
  xor128(b4, b4, t4);
  mix32_00100212_01110313(k2,k3);


  add2x(k0,k0,t);
  permute32_0213(k5);


  mul2x32_0101(p4,a2,c0);
  store128((mem128)adr1,b4); adr1+=16;

  //##############################################################;


  //#---------------;//#;
  //# Mul by Const2; //#;
  //#---------------;//#;


  mul2x32_0101(p0,a0,c0);
  mul2x32_2301(p1,a0,c0);

  set_lane_64_0010(a2,k5);
  set_lane_64_0011(b2,t2);

  shiftur2x(t,p4,25);
  mix32_00100212_01110313(k0,k1);

  and128(p4, p4, mask25);
  permute32_0213(k2);

  add2x(p0,p0,t);
  permute32_0213(k0);

  mul2x32_0101(p2,a1,c0);

  shiftur2x(t,p0,26);
  and128(p0, p0, mask26);

  adr1 = input_1 + 32;
  store128((mem128)adr1,b2); adr1+=16;

  add2x(p1,p1,t);

  adr0 = input_0 + 32;
  store128((mem128)adr0,a2); adr0+=16;

  mul2x32_2301(p3,a1,c0);

  shiftur2x(t,p1,25);
  store128((mem128)adr0,k0); adr0+=16;
  and128(p1, p1, mask25);
  store128((mem128)adr0,k2); adr0+=16;

  mul2x32_2323(q5,a2,c0);

  add2x(p2,p2,t);
  mix32_00100212_01110313(p0,p1);



  //##############################################################;


  //#---------------;//#;
  //# Mul by Const2; //#;
  //#---------------;//#;




  //#--;

  adr5 = input_5;
  adr5 += 80;
  load128(_28_27_28_27,(mem128)adr5);
  shiftur2x(t,p2,26); //#p;
  and128(p2, p2, mask26); //#p;

  sub4x(na0,_28_27_28_27,p0); //#p;
  add2x(p3,p3,t); //#p;

  mul2x32_0123(q0,k0,c0);
  shiftur2x(t,p3,25); //#p;
  and128(p3, p3, mask25); //#p;

  shiftur2x(t2,q5,25);
  and128(q5, q5, mask25);
  add2x(q0,q0,t2);

  mul2x32_2323(q1,k0,c0);

  add2x(p4,p4,t); //#p;
  mix32_00100212_01110313(p2,p3); //#p;


  shiftur2x(t2,q0,26);
  and128(q0, q0, mask26);

  mul2x32_0123(q2,k2,c0);
  sub4x(na1,_28_27_28_27,p2); //#p;
  add2x(q1,q1,t2);

  mul2x32_2323(q3,k2,c0);

  //# negate; //#;
  shiftur2x(t2,q1,25);
  and128(q1, q1, mask25);
  add2x(q2,q2,t2);

  set_lane_64_1001(na0,p0); //#p;
  set_lane_64_1001(na1,p2); //#p;


  mix32_00100212_01110313(q0,q1);
  shiftur2x(t2,q2,26);

  permute32_0213(na0); //#p;
  and128(q2, q2, mask26);

  sub4x(n0,_28_27_28_27,q0); //#qq;

  add2x(q3,q3,t2);
  permute32_0213(na1); //#p;

  //## serial carry; //##;

  adr5 = input_5;
  adr5 += 64;
  load128(_27,(mem128)adr5); adr5+=16;
  load128(_28_27_28_27,(mem128)adr5);


  shiftur2x(t2,q3,25);
  and128(q3, q3, mask25);
  add2x(q5,q5,t2);


  //##----------------;//##;



  //# arrange; //#;

  mix32_00100212_01110313(q2,q3)	;//# latency;
  mix32_00100212_01110313(p4,q5);


  //# negate; //#;

  sub4x(n1,_28_27_28_27,q2); //#qq;
  sub4x(n2,_27,p4); //#qq			# latency;

  permute32_0213(n0); //#qq;
  permute32_0213(n1); //#qq;




  adr0 = input_0 + 48;



  //## Hadamard; //## ----------------------------------------------------;

  //## x3 y3 z3 t3; //##;

  mix32_11121320(q0,n2,p4); //#qq		# prev.;
  add4x(sum1,na1,n1);
  store128((mem128)adr0,n0); adr0+=16	;//# prev. mul const 2;
  permute32_3012(p4,q0); //#qq		# prev.;
  sub4x(dif1,na1,n1);
  store128((mem128)adr0,n1); adr0+=16	;//# prev. mul const 2;
  permute32_0213(p4); //#qq		# prev.;

  mix32_00100212_01110313(sum1,dif1);

  add4x(sum0,na0,n0);
  swap64_00100111(sum1,p4);
  sub4x(dif0,na0,n0);
  swap64_00111001(p4,dif1);

  add4x(a1,sum1,dif1);
  sub4x(a4,sum1,dif1);

  mix32_00100212_01110313(sum0,dif0);

  add4x(a0,sum0,dif0);
  swap64_10010011(a1,p4);

  sub4x(a3,sum0,dif0);
  swap64_00100111(p4,a4);

  mix32_00010212_10110323(a1,a4);

  adr5 = input_5;
  adr5 += 32;

  add4x(sum1,a1,a4);
  load128(_28,(mem128)adr5); adr5+=16;

  sub4x(dif1,a1,a4);
  load128(_29_28,(mem128)adr5);


  swap64_00100111(p4,sum1);
  add4x(a0,a0,_29_28);

  swap64_00100111(sum1,dif1);
  add4x(a3,a3,_29_28);

  add4x(a4,sum1,_29_28);
  add4x(a1,p4,_29_28);
  add4x(a2,dif1,_28);




  //#=============;//#;
  //# First Inpu;t //#;
  //# x3 y3 z3 t3; //#;
  //#=============;//#;


  //## First half; //##;

  swap64_00100111(a0,a3);
  add2x(_2a1,a1,a1);
  add2x(_2a2,a2,a2);
  add2x(_2a0,a3,a3);
  swap64_00100111(a0,a3);
  add2x(_2a4,a4,a4);

  //#----------;//#;
  //# Squaring; //#;
  //#----------;//#;

  mul2x32_0101(h3,a2,a2);
  mul2x32_2301_ac(h3,_2a1,a0);
  mul2x32_0123_ac(h3,_2a1,a0);

  mul2x32_0101(h4,a1,a1);
  mul2x32_0101_ac(h4,_2a2,a0);
  mul2x32_2301_ac(h4,_2a1,_2a0);

  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  mul2x32_0101(h0,a0,a0);
  add2x(h4,h4,t);
  mul2x32_0101_ac(h0,_2a2,_2a0);
  mul2x32_2301_ac(h0,_2a1,_2a1);

  shiftur2x(t,h4,25);
  and128(h4, h4, mask25);

  mul2x32_2323(h1,_2a1,a1);
  add2x(h0,h0,t);
  mul2x32_0101_ac(h1,_2a0,a0);
  mul2x32_0101_ac(h1,_2a2,a1);

  shiftur2x(t,h0,26);
  and128(h0, h0, mask26);

  mul2x32_0123(h2,_2a0,a0);
  add2x(h1,h1,t);
  mul2x32_0101_ac(h2,_2a1,a0);
  mul2x32_0123_ac(h2,_2a2,_2a1);

  shiftur2x(t,h1,25);
  and128(h1, h1, mask25);

  mul2x32_2323(k3,a2,a2);
  add2x(h2,h2,t);
  mix32_00100212_01110313(h0,h1);
  mul2x32_2301_ac(k3,_2a4,a3);
  mul2x32_0123_ac(k3,_2a4,a3);

  shiftur2x(t,h2,26);
  and128(h2, h2, mask26);
  permute32_0213(h0);

  mul2x32_0101(k4,a4,a4);
  add2x(h3,h3,t);
  mul2x32_2301_ac(k4,_2a2,a3);
  mul2x32_2323_ac(k4,_2a4,_2a0);

  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  adr0 = input_0;
  store128((mem128)adr0,h0); adr0+=16;

  mul2x32_0101(k0,a3,a3);
  add2x(h4,h4,t);
  shiftur2x(t2,k3,25);
  mix32_00100212_01110313(h2,h3);
  and128(k3, k3, mask25);

  mul2x32_2323_ac(k0,_2a2,_2a0);
  add2x(k4,k4,t2);
  permute32_0213(h4);
  mul2x32_2301_ac(k0,_2a4,_2a4);
  shiftur2x(t2,k4,25);
  permute32_0213(h2);


  //# arrange; //#;

  and128(k4, k4, mask25);

  set_lane_64_1001(a2,h4);
  store128((mem128)adr0,h2); adr0+=16;

  //#----------;//#;
  //# Squaring; //#;
  //#----------;//#;


  mul2x32_2323(k1,_2a4,a4)	;
  add2x(k0,k0,t2);
  mul2x32_2301_ac(k1,_2a0,a3);
  mul2x32_2301_ac(k1,_2a2,a4);

  shiftur2x(t2,k0,26);
  and128(k0, k0, mask26);

  mul2x32_2323(k2,_2a0,a3);
  add2x(k1,k1,t2);
  mul2x32_0101_ac(k2,_2a4,a3);
  mul2x32_2323_ac(k2,_2a2,_2a4);

  shiftur2x(t2,k1,25);

  adr2 = input_2;
  load128(b0,(mem128)adr2); adr2+=16;

  and128(k1, k1, mask25);

  adr0 = input_0;
  load128(a0,(mem128)adr0); adr0+=16;

  mul2x32_2301(h1,a0,b0)	;

  add2x(k2,k2,t2);
  mix32_00100212_01110313(k0,k1);

  mul2x32_0123_ac(h1,a0,b0)	;

  shiftur2x(t2,k2,26);
  permute32_0213(k0);
  and128(k2, k2, mask26);

  adr0 = input_0 + 16;
  load128(a1,(mem128)adr0); adr0+=16;

  mul2x32_0101(h0,a0,b0);


  add2x(k3,k3,t2);

  adr0 = input_0 + 48;
  store128((mem128)adr0,k0); adr0+=16;

  mul2x32_2301(h3,a1,b0)	;
  mul2x32_0123_ac(h3,a1,b0);

  shiftur2x(t2,k3,25);
  and128(k3, k3, mask25);
  swap64_00100111(a0,k0);

  add2x(_2a1,a1,a1);
  load128(b1,(mem128)adr2); adr2+=16;

  mul2x32_0101_ac(h3,k0,b1)	;

  add2x(k4,k4,t2);
  mix32_00100212_01110313(k2,k3);

  mul2x32_0123_ac(h3,a0,b1);
  add2x(_2a0,k0,k0);
  permute32_0213(k4);


  permute32_0213(k2);

  mul2x32_0101(h2,a1,b0)	;

  set_lane_64_0010(a2,k4);

  adr0 = input_0 + 64;
  store128((mem128)adr0,k2); adr0+=16;

  add2x(_2a2,a2,a2);
  swap64_00100111(a0,k0);

  adr2 = input_2 + 32;
  load128(b2,(mem128)adr2); adr2+=16;

  adr0 = input_0 + 32;
  store128((mem128)adr0,a2); adr0+=16	;//# prev. sqr;
  store128((mem128)adr0,k0); adr0+=16	;//# prev. sqr;


  //#----------------;//#;
  //# Multiplication; //#;
  //#----------------;//#;

  mul2x32_0101_ac(h3,a2,b2)	;

  mul2x32_0101(h4,a2,b0);
  mul2x32_2323_ac(h4,_2a1,b0);
  mul2x32_0101_ac(h4,a1,b1);
  mul2x32_0123_ac(h4,_2a0,b1);
  mul2x32_0101_ac(h4,a0,b2);

  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  mul2x32_0123_ac(h0,_2a2,b0);
  add2x(h4,h4,t);
  mul2x32_2301_ac(h0,_2a1,b1)	;
  mul2x32_0123_ac(h0,_2a1,b1);
  mul2x32_0101_ac(h0,_2a0,b2);

  shiftur2x(t,h4,25);
  and128(h4, h4, mask25);

  mul2x32_0101_ac(h1,a2,b1)	;
  add2x(h0,h0,t);
  adr5 = input_5;
  adr5 += 16;
  load128(mask26,(mem128)adr5);
  mul2x32_2323_ac(h1,_2a1,b1)	;
  mul2x32_0101_ac(h1,a1,b2);

  shiftur2x(t,h0,26);
  and128(h0, h0, mask26);

  mul2x32_0123_ac(h2,_2a0,b0)	;
  add2x(h1,h1,t);
  mul2x32_0101_ac(h2,a0,b1)	;
  mul2x32_0123_ac(h2,_2a2,b1);
  mul2x32_2301_ac(h2,_2a1,b2);


  //## serial carry; //##;

  shiftur2x(t,h1,25);
  and128(h1, h1, mask25);

  mul2x32_2323(k3,a2,b2)	;

  add2x(h2,h2,t);
  mix32_00100212_01110313(h0,h1);

  mul2x32_2323(k0,_2a0,b2)	;

  shiftur2x(t,h2,26);
  permute32_0213(h0);

  and128(h2, h2, mask26);

  adr2 = input_2 + 48;
  load128(b3,(mem128)adr2); adr2+=16;

  add2x(h3,h3,t);

  adr0 = input_0;
  store128((mem128)adr0,h0); adr0+=16;

  mul2x32_2323_ac(k0,_2a2,b3);

  shiftur2x(t,h3,25);
  adr0 = input_0 + 48;
  load128(a3,(mem128)adr0); adr0+=16;

  and128(h3, h3, mask25);
  load128(a4,(mem128)adr0); adr0+=16;

  mul2x32_2301(k4,a2,b3)	;

  add2x(h4,h4,t);
  mix32_00100212_01110313(h2,h3);


  add2x(_2a4,a4,a4);
  load128(b4,(mem128)adr2); adr2+=16;

  mul2x32_2301_ac(k3,a4,b3)	;



  //#----------------;//#;
  //# Multiplication; //#;
  //#----------------;//#;

  permute32_0213(h2);

  mul2x32_0123_ac(k3,a4,b3)	;
  mul2x32_2301_ac(k3,a3,b4);
  mul2x32_0123_ac(k3,a3,b4);

  mul2x32_2323_ac(k4,_2a4,b3);
  mul2x32_0101_ac(k4,a4,b4);
  mul2x32_2323_ac(k4,_2a0,b4)	;
  mul2x32_0123_ac(k4,a3,b2);

  mul2x32_2323(k2,_2a2,b4);
  mul2x32_2323_ac(k2,_2a0,b3);

  shiftur2x(t2,k3,25);
  and128(k3, k3, mask25);

  adr0 = input_0 + 16			;//# prev.;
  store128((mem128)adr0,h2); adr0+=16	;//# prev.;

  mul2x32_0101_ac(k0,a3,b3)	;
  add2x(k4,k4,t2);
  mul2x32_2301_ac(k0,_2a4,b4);
  mul2x32_0123_ac(k0,_2a4,b4);

  shiftur2x(t2,k4,25);
  and128(k4, k4, mask25);

  mul2x32_2301(k1,a3,b3)	;
  add2x(k0,k0,t2);
  mul2x32_0123_ac(k1,a3,b3);
  mul2x32_2301_ac(k1,a2,b4);
  mul2x32_2323_ac(k1,_2a4,b4);
  mul2x32_0123_ac(k1,a4,b2);

  shiftur2x(t2,k0,26);
  and128(k0, k0, mask26);

  mul2x32_0101_ac(k2,a4,b3)	;
  add2x(k1,k1,t2);
  mul2x32_0101_ac(k2,a3,b4);
  mul2x32_2323_ac(k2,_2a4,b2);

  //## serial carry; //##;

  shiftur2x(t2,k1,25);
  adr1 = input_1;
  load128(b0,(mem128)adr1); adr1+=16;

  and128(k1, k1, mask25);
  load128(b1,(mem128)adr1); adr1+=16;

  adr1 = input_1 + 48;
  load128(b3,(mem128)adr1); adr1+=16;

  mul2x32_0101(h0,b0,b0)	;

  add2x(k2,k2,t2);
  mix32_00100212_01110313(k0,k1);

  mul2x32_0101(h5,b1,b1)	;

  shiftur2x(t2,k2,26);
  swap64_00100111(b0,b3);
  and128(k2, k2, mask26);
  permute32_0213(k0);
  add2x(k3,k3,t2);

  adr1 = input_1 + 32;
  load128(b2,(mem128)adr1); adr1+=16;
  mul2x32_0101(h3,b2,b2)	;

  shiftur2x(t2,k3,25);
  and128(k3, k3, mask25);

  add2x(_2b0,b3,b3);
  add2x(_2b1,b1,b1);

  adr0 = input_0 + 48;
  store128((mem128)adr0,k0); adr0+=16;

  add2x(k4,k4,t2);
  mix32_00100212_01110313(k2,k3);

  //##----------------;//##;

  add2x(_2b2,b2,b2);
  swap64_00100111(b0,b3);
  mul2x32_2301_ac(h0,_2b1,_2b1)	;

  mul2x32_0101_ac(h0,_2b2,_2b0)	;
  mul2x32_2323(h1,_2b1,b1);

  mul2x32_0101_ac(h1,_2b0,b0)	;
  mul2x32_0101_ac(h1,_2b2,b1);


  adr5 = input_5;
  adr5 += 16;
  load128(mask26,(mem128)adr5);
  shiftur2x(t,h0,26);
  permute32_0213(k2);
  and128(h0, h0, mask26);
  mix32_00100212_01110313(h4,k4);

  store128((mem128)adr0,k2); adr0+=16;

  mul2x32_0123(h2,_2b0,b0)	;

  add2x(h1,h1,t);
  permute32_0213(h4);

  mul2x32_0101_ac(h2,_2b1,b0)	;


  //#------------------------------------------------------------------------------------;
  //#------------------------------------------------------------------------------------;
  //#------------------------------------------------------------------------------------;
  //#------------------------------------------------------------------------------------;





  //#==============;//#;
  //# Second Inpu;t //#;
  //# x2 y2 z2 t2;  //#;
  //#==============;//#;

  //## First half; //##;

  //#---------------------------------------;//#;
  //# Squaring;                              //#;
  //# x2 y2 z2 t2 = x2*x2 y2*y2 z2*z2 t2*t2; //#;
  //#---------------------------------------;//#;


  mul2x32_0123_ac(h2,_2b2,_2b1)	;

  shiftur2x(t,h1,25);
  adr5 = input_5;
  load128(mask25,(mem128)adr5);

  and128(h1, h1, mask25);
  adr0 = input_0 + 32			;//# prev.;
  store128((mem128)adr0,h4); adr0+=16	;//# prev.;


  mul2x32_2301_ac(h3,_2b1,b0)	;
  add2x(h2,h2,t);
  mul2x32_0123_ac(h3,_2b1,b0)	;

  shiftur2x(t,h2,26);
  and128(h2, h2, mask26);

  mul2x32_0101_ac(h5,_2b2,b0)	;
  add2x(h3,h3,t);
  mul2x32_2301_ac(h5,_2b1,_2b0)	;

  //## serial carry; //##;
  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  mul2x32_0101(k0,b3,b3)	;

  add2x(h5,h5,t);
  mix32_00100212_01110313(h2,h3);

  mul2x32_2323_ac(k0,_2b2,_2b0)	;

  shiftur2x(t,h5,25);
  permute32_0213(h2);
  and128(h5, h5, mask25);

  mul2x32_2301(k1,_2b0,b3)	;

  add2x(h0,h0,t);
  permute32_0213(h5);

  mul2x32_2323(k3,b2,b2)	;

  shiftur2x(t,h0,26);

  adr1 = input_1 + 16;
  store128((mem128)adr1,h2); adr1+=16;

  and128(h0, h0, mask26);

  adr1 = input_1 + 64;
  load128(b4,(mem128)adr1); adr1+=16;

  add2x(h1,h1,t);
  set_lane_64_1001(a2,h5);

  //##----------------;//##;

  //# arrange; //#;

  mul2x32_2301_ac(k1,_2b2,b4)	;

  add2x(_2b4,b4,b4);
  mix32_00100212_01110313(h0,h1);

  mul2x32_2323(k2,_2b0,b3)	;
  mul2x32_2301_ac(k0,_2b4,_2b4);
  mul2x32_2323_ac(k1,_2b4,b4);

  mul2x32_0101_ac(k2,_2b4,b3)	;
  mul2x32_2323_ac(k2,_2b2,_2b4);

  shiftur2x(t2,k0,26);
  and128(k0, k0, mask26);

  add2x(k1,k1,t2);
  permute32_0213(h0);

  mul2x32_2301_ac(k3,_2b4,b3)	;

  shiftur2x(t2,k1,25);
  and128(k1, k1, mask25);

  add2x(k2,k2,t2);
  adr1 = input_1;
  store128((mem128)adr1,h0); adr1+=16;


  //##################;


  //## Second half; //##;




  //#---------------------------------------;//#;
  //# Squaring;                              //#;
  //# x2 y2 z2 t2 = x2*x2 y2*y2 z2*z2 t2*t2; //#;
  //#---------------------------------------;//#;

  mul2x32_0123_ac(k3,_2b4,b3)	;

  shiftur2x(t2,k2,26);
  and128(k2, k2, mask26);

  adr3 = input_3 + 16		;//#;
  load128(c0,(mem128)adr3)	;//#;

  mul2x32_0101(k4,b4,b4)	;
  add2x(k3,k3,t2);
  mul2x32_2301_ac(k4,_2b2,b3)	;
  mul2x32_2323_ac(k4,_2b4,_2b0);


  //## serial carry; //##;

  shiftur2x(t2,k3,25);
  adr1 = input_1;
  load128(b0,(mem128)adr1); adr1+=16;

  and128(k3, k3, mask25);
  load128(b1,(mem128)adr1); adr1+=16;

  mul2x32_0101(h0,b0,c0)	;

  add2x(k4,k4,t2);

  mul2x32_2301(h1,b0,c0)	;
  mul2x32_0101(h2,b1,c0);

  shiftur2x(t2,k4,25);
  mix32_00100212_01110313(k2,k3);
  and128(k4, k4, mask25);
  add2x(k0,k0,t2);
  permute32_0213(k2);

  mul2x32_2301(h3,b1,c0)	;

  shiftur2x(t,h1,25);
  and128(h1, h1, mask25);
  add2x(h2,h2,t);

  shiftur2x(t2,k0,26);
  permute32_0213(k4);

  and128(k0, k0, mask26);
  add2x(k1,k1,t2);
  set_lane_64_0010(a2,k4);

  //##----------------;//##;

  shiftur2x(t,h2,26);
  and128(h2, h2, mask26);

  add2x(h3,h3,t);
  mix32_00100212_01110313(k0,k1);

  mul2x32_0101(h4,a2,c0)	;

  shiftur2x(t,h3,25);
  and128(h3, h3, mask25);

  mul2x32_0123(p2,k2,c0)	;
  add2x(h4,h4,t);
  permute32_0213(k0);

  mul2x32_2323(p3,k2,c0)	;

  shiftur2x(t,h4,25);
  and128(h4, h4, mask25);
  add2x(h0,h0,t);

  shiftur2x(t2,p2,26);
  and128(p2, p2, mask26);
  add2x(p3,p3,t2);

  adr1 = input_1 + 48;
  store128((mem128)adr1,k0); adr1+=16;


  //##################;

  //#---------------;//#;
  //# Mul by Const2; //#;
  //#---------------;//#;


  //## serial carry; //##;

  mul2x32_2323(p5,a2,c0)	;

  shiftur2x(t2,p3,25);
  and128(p3, p3, mask25);

  shiftur2x(t,h0,26);
  and128(h0, h0, mask26);
  add2x(h1,h1,t);
  mix32_00100212_01110313(h2,h3);

  adr5 = input_5;
  adr5 += 80;

  add2x(p5,p5,t2);
  load128(_28_27_28_27,(mem128)adr5);

  mul2x32_0123(p0,k0,c0)	;

  shiftur2x(t2,p5,25);
  and128(p5, p5, mask25);


  //# negate; //#;

  sub4x(n1,_28_27_28_27,h2);
  mix32_00100212_01110313(h0,h1);

  add2x(p0,p0,t2);

  sub4x(n0,_28_27_28_27,h0);
  set_lane_64_0011(h2,n1);


  mul2x32_2323(p1,k0,c0)	;

  shiftur2x(t2,p0,26);
  mix32_00100212_01110313(h4,p5);
  and128(p0, p0, mask26);
  ;
  adr5 = input_5;
  adr5 += 64;
  load128(_27,(mem128)adr5);

  set_lane_64_0011(h0,n0);

  add2x(p1,p1,t2);
  permute32_0213(h2);

  sub4x(n2,_27,h4);
  permute32_0213(h0);



  //#---------------;//#;
  //# Mul by Const2; //#;
  //#---------------;//#;


  //## serial carry; //##;

  shiftur2x(t2,p1,25)	;//# latency;
  and128(p1, p1, mask25);
  add2x(p2,p2,t2);



  //##----------------;//##;


  //# arrange; //#;

  adr5 = input_5;
  adr5 += 80;
  load128(_28_27_28_27,(mem128)adr5);

  mix32_11121320(p5,n2,h4);
  mix32_00100212_01110313(p0,p1);
  mix32_00100212_01110313(p2,p3);

  //# negate; //#;


  sub4x(n0,_28_27_28_27,p0)	;//# latency;
  sub4x(n1,_28_27_28_27,p2);
  permute32_3012(p4,p5);

  permute32_0213(n0);
  permute32_0213(n1);
  permute32_0213(p4);



  //## Hadamard; //##-----------------------------------------------------------------------------;
  //## x2 y2 z2 t2; //##;

  //#--;

  //#add4x(sum0,h0,n0);
  //#sub4x(dif0,h0,n0);
  //#;
  //#add4x(sum1,h2,n1);
  //#sub4x(dif1,h2,n1);
  //#;
  //#adr5 = input_5;
  //#adr5 += 32;
  //#;
  //#mix32_00100212_01110313(sum0,dif0);
  //#mix32_00100212_01110313(sum1,dif1);
  //#;
  //#add4x(a0,sum0,dif0);
  //#load128(_28,(mem128)adr5); adr5+=16;
  //#;
  //#sub4x(a3,sum0,dif0);
  //#load128(_29_28,(mem128)adr5);
  //#;
  //#add4x(a0,a0,_29_28);
  //#swap64_00100111(sum1,p4);
  //#;
  //#add4x(a3,a3,_29_28);
  //#swap64_00111001(p4,dif1);
  //#;
  //#add4x(a1,sum1,dif1);
  //#sub4x(a4,sum1,dif1);
  //#;
  //#swap64_10010011(a1,p4);
  //#swap64_00100111(p4,a4);
  //#;
  //#mix32_00010212_10110323(a1,a4);
  //#;
  //#add4x(sum1,a1,a4);
  //#sub4x(dif1,a1,a4);
  //#;
  //#swap64_00100111(p4,sum1);
  //#swap64_00100111(sum1,dif1);
  //#;
  //#add4x(a1,p4,_29_28);
  //#add4x(a4,sum1,_29_28);
  //#add4x(a2,dif1,_28);
  //#;
  //#adr1 = input_1 + 64;
  //#store128((mem128)adr1,a4); adr1 +=16;

  //#--;

  add4x(sum1,h2,n1);
  sub4x(dif1,h2,n1);

  mix32_00100212_01110313(sum1,dif1);

  add4x(sum0,h0,n0);
  swap64_00100111(sum1,p4);
  sub4x(dif0,h0,n0);
  swap64_00111001(p4,dif1);

  add4x(a1,sum1,dif1);
  sub4x(a4,sum1,dif1);

  mix32_00100212_01110313(sum0,dif0);

  add4x(a0,sum0,dif0);
  swap64_10010011(a1,p4);
  sub4x(a3,sum0,dif0);
  swap64_00100111(p4,a4);

  mix32_00010212_10110323(a1,a4);

  add4x(sum1,a1,a4);
  adr5 = input_5;
  adr5 += 32;
  load128(_28,(mem128)adr5); adr5+=16;

  sub4x(dif1,a1,a4);
  load128(_29_28,(mem128)adr5);

  add4x(a0,a0,_29_28);
  swap64_00100111(p4,sum1);
  add4x(a3,a3,_29_28);
  swap64_00100111(sum1,dif1);

  add4x(a1,p4,_29_28);
  add4x(a4,sum1,_29_28);
  add4x(a2,dif1,_28);


  //#-----------------------------;


  swap64_00100111(a0,a3);
  add2x(_2a1,a1,a1);
  add2x(_2a2,a2,a2);
  add2x(_2a0,a3,a3);

  adr1 = input_1 + 64			;//# prev.;
  store128((mem128)adr1,a4); adr1 +=16	;//# prev.;


  //## First half; //##;

  //#----------;//#;
  //# Squaring; //#;
  //#----------;//#;

  mul2x32_0101(k0,a0,a0)	;
  mul2x32_0101_ac(k0,_2a2,_2a0);
  mul2x32_2301_ac(k0,_2a1,_2a1);
  swap64_00100111(a0,a3);

  mul2x32_2323(k1,_2a1,a1);
  mul2x32_0101_ac(k1,_2a0,a0);
  mul2x32_0101_ac(k1,_2a2,a1);

  shiftur2x(t,k0,26);
  and128(k0, k0, mask26);

  mul2x32_0123(k2,_2a0,a0)	;
  add2x(k1,k1,t);
  mul2x32_0101_ac(k2,_2a1,a0)	;
  mul2x32_0123_ac(k2,_2a2,_2a1);

  shiftur2x(t,k1,25);
  and128(k1, k1, mask25);

  mul2x32_0101(k3,a2,a2)	;
  add2x(k2,k2,t);
  mul2x32_2301_ac(k3,_2a1,a0)	;
  mul2x32_0123_ac(k3,_2a1,a0);

  shiftur2x(t,k2,26);
  and128(k2, k2, mask26);

  mul2x32_0101(k4,a1,a1)	;
  add2x(k3,k3,t);
  mul2x32_0101_ac(k4,_2a2,a0);
  mul2x32_2301_ac(k4,_2a1,_2a0);


  //## serial carry; //##;

  shiftur2x(t,k3,25);
  and128(k3, k3, mask25);
  mul2x32_0101(h0,a3,a3)	;
  add2x(k4,k4,t);

  mul2x32_2323_ac(h0,_2a2,_2a0)	;
  shiftur2x(t,k4,25);
  mix32_00100212_01110313(k2,k3);
  and128(k4, k4, mask25);
  add2x(k0,k0,t);
  permute32_0213(k2);

  mul2x32_2301(h1,_2a0,a3)	;
  shiftur2x(t,k0,26);
  permute32_0213(k4);
  and128(k0, k0, mask26);
  add2x(k1,k1,t);

  //##----------------;//##;

  mul2x32_2301(h5,_2a2,a3)	;
  //# arrange; //#;
  adr1 = input_1 +64;
  load128(a4,(mem128)adr1); adr1+=16;

  add2x(_2a4,a4,a4);
  mix32_00100212_01110313(k0,k1);


  set_lane_64_1001(a2,k4);
  mul2x32_2301_ac(h0,_2a4,_2a4)	;
  mul2x32_2323_ac(h1,_2a4,a4);
  mul2x32_2301_ac(h1,_2a2,a4);
  mul2x32_2323(h3,a2,a2);

  shiftur2x(t2,h0,26);
  permute32_0213(k0);
  and128(h0, h0, mask26);

  add2x(h1,h1,t2);

  adr1 = input_1;
  store128((mem128)adr1,k0); adr1+=16;



  //## Second half; //##;

  //#----------;//#;
  //# Squaring; //#;
  //#----------;//#;

  mul2x32_2323(h2,_2a0,a3)	;
  mul2x32_0101_ac(h2,_2a4,a3);
  mul2x32_2323_ac(h2,_2a2,_2a4);

  shiftur2x(t2,h1,25);
  and128(h1, h1, mask25);
  store128((mem128)adr1,k2); adr1+=16	;//# prev.;

  mul2x32_2301_ac(h3,_2a4,a3)	;
  add2x(h2,h2,t2);
  mul2x32_0123_ac(h3,_2a4,a3)	;

  shiftur2x(t2,h2,26);
  //#h2 &= mask26;
  and128(b4, h2, mask26);//### change h2 to b4;

  mul2x32_0101_ac(h5,a4,a4)	;
  add2x(h3,h3,t2);
  mul2x32_2323_ac(h5,_2a4,_2a0)	;

  shiftur2x(t2,h3,25);
  adr3 = input_3;
  load128(c0,(mem128)adr3);

  and128(h3, h3, mask25);

  adr1 = input_1;
  load128(b0,(mem128)adr1); adr1+=16;

  mul2x32_0101(k0,b0,c0)	;
  add2x(h5,h5,t2);

  //## serial carry; //##;

  mul2x32_2301(k1,b0,c0)	;
  shiftur2x(t2,h5,25);
  //#mix32_00100212_01110313(h2,h3);
  mix32_00100212_01110313(b4,h3);
  and128(h5, h5, mask25);
  add2x(h0,h0,t2);
  permute32_0213(b4);

  shiftur2x(t2,k0,26);
  and128(k0, k0, mask26);
  add2x(k1,k1,t2);

  shiftur2x(t2,h0,26);
  permute32_0213(h5);
  //#h0 &= mask26	;
  and128(b3, h0, mask26);//### change h0 to b3;
  //##----------------;//##;

  adr1 = input_1 + 16;
  load128(b1,(mem128)adr1); adr1+=16;
  mul2x32_0101(k2,b1,c0)	;

  add2x(h1,h1,t2);
  set_lane_64_0010(a2,h5);

  shiftur2x(t2,k1,25);
  and128(k1, k1, mask25);
  add2x(k2,k2,t2);


  //# arrange; //#;

  mul2x32_2301(k3,b1,c0)	;
  mul2x32_0101(k4,a2,c0);
  shiftur2x(t2,k2,26);
  //#mix32_00100212_01110313(h0,h1);
  mix32_00100212_01110313(b3,h1);
  and128(k2, k2, mask26);
  add2x(k3,k3,t2);

  //#permute32_0213(h0);
  permute32_0213(b3);



  //#---------------;//#;
  //# Mul by Const1; //#;
  //#---------------;//#;


  //## First half; //##;

  mul2x32_0123(h0,b3,c0)	;

  //## serial carry; //##;

  shiftur2x(t2,k3,25);
  and128(k3, k3, mask25);
  add2x(k4,k4,t2);

  mul2x32_2323(h1,b3,c0)	;

  shiftur2x(t2,k4,25);
  and128(k4, k4, mask25);
  mix32_00100212_01110313(k2,k3);
  add2x(k0,k0,t2);

  //##----------------;//##;

  //# arrange; //#;


  adr5 = input_5;
  adr5 += 80;
  load128(_28_27_28_27,(mem128)adr5);

  sub4x(n1,_28_27_28_27,k2);

  //# negate; //#;

  shiftur2x(t2,h0,26);
  and128(h0, h0, mask26);
  mix32_00100212_01110313(k0,k1);
  add2x(h1,h1,t2);

  mul2x32_0123(h2,b4,c0)	;
  sub4x(n0,_28_27_28_27,k0);
  set_lane_64_0011(n1,k2);
  set_lane_64_0011(n0,k0);

  shiftur2x(t2,h1,25);
  permute32_0213(n1);
  and128(h1, h1, mask25);
  permute32_0213(n0);
  add2x(h2,h2,t2);

  mul2x32_2323(h3,b4,c0)	;
  shiftur2x(t2,h2,26);


  adr1 = input_1;
  store128((mem128)adr1,n0); adr1+=16;
  and128(h2, h2, mask26);
  store128((mem128)adr1,n1); adr1+=16;







  //#--------------------------------------------;


  //#---------------;//#;
  //# Mul by Const1; //#;
  //#---------------;//#;

  mul2x32_2323(h5,a2,c0)	;
  add2x(h3,h3,t2);


  //## serial carry; //##;


  shiftur2x(t2,h3,25);
  and128(h3, h3, mask25);
  add2x(h5,h5,t2);

  shiftur2x(t2,h5,25);
  and128(h5, h5, mask25);
  add2x(h0,h0,t2);

  //##----------------;//##;


  //# arrange; //#;

  adr5 = input_5;
  adr5 += 64;
  load128(_27,(mem128)adr5);

  mix32_00100212_01110313(k4,h5);
  mix32_00100212_01110313(h2,h3);
  mix32_00100212_01110313(h0,h1);

  sub4x(n2,_27,k4);

  permute32_0213(h2);
  permute32_0213(h0);


  //# negate; //#;


  mix32_11121320(h1,k4,n2);

  adr1 = input_1 + 64;
  store128((mem128)adr1,h2);
  adr1 -= 16;
  store128((mem128)adr1,h0); adr1+=16;

  permute32_3012(h4,h1);
  permute32_0213(h4);


  adr1 = input_1 + 32;
  store128((mem128)adr1,h4); adr1+=16;


  count -= 1;
  if ((int)count >= 0) goto looptop;




  //#------------------------------;

  /*caller_r4 = stack_r4;
    caller_r5 = stack_r5;
    caller_r6 = stack_r6;
    caller_r7 = stack_r7;
    caller_r8 = stack_r8;
    caller_r9 = stack_r9;
    caller_r10 = stack_r10;
    caller_r11 = stack_r11;
    caller_r12 = stack_r12;
    caller_r14 = stack_r14;


    qpopreturn;*/

}

