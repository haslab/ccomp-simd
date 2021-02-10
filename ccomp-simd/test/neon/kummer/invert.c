#include "myneon.h"

void invert(address input_0, address input_1) {
  address adr0, adr1;
  int128 a0, a1, a2, a3, a4;
  int128 b0, b1, b2, b3, b4;
  int128 _2a0, _2a1, _2a2, _2a3, _2a4;
  int128 h0, h1, h2, h3, h4, h5;
  int128 r0, r1, r2, r3, r4, r5;
  int128 _2h0, _2h1, _2h2, _2h3, _2h4;
  int128 k0, k1, k2, k3, k4;
  int128 _2k0, _2k1, _2k2, _2k3, _2k4;
  int128 s4, t, mask25, mask26;
  address ptr0, ptr1;
  int32 ctr;
  //stack3072 ptr_stack;
  unsigned char ptr_stack[3072/8];

  /*qpushenter invert ;

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
    stack_r14 = caller_r14;
    
    stack128 caller_q4_stack;
    stack128 caller_q5_stack;
    stack128 caller_q6_stack;
    stack128 caller_q7_stack;*/

  ptr0 = ptr_stack;
  ptr1 = ptr0;
  set2x(mask25,0xffffffff);
  shiftl4x_in(mask25,7);
  shiftur2x_in(mask25,7);
  set2x(mask26,0xffffffff);
  shiftl4x_in(mask26,6);
  shiftur2x_in(mask26,6);
  store128((mem128)ptr1,mask25); ptr1+=16		;//# s + 16;

  //###############################;
  //# sqr mul sqr sqr mul sqr mul; //#;
  //###############################;


  //#============;//#;
  //# First Half; //#;
  //#============;//#;

  adr1 = input_1;
  load128(a0,(mem128)adr1); adr1+=16;
  load128(a1,(mem128)adr1); adr1+=16;
  load128(a2,(mem128)adr1); adr1+=16;

  //## sqr : x2; //##;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;
  
  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;
  
  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;
  
  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;

  
  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);


  //# arrange; //#;
  
  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);
  //##-----;//##;



  //## mul : x3; //##;
  
  mul2x32_0101(k0,h0,a0)		;//#   b0 a0;
  mul2x32_2301(k1,h0,a0)		;//#   b1 a0;
  mul2x32_0101(k2,h2,a0)		;//#   b2 a0;
  mul2x32_2301(k3,h2,a0)		;//#   b3 a0;
  mul2x32_0101(k4,h4,a0)		;//#   b4 a0;

  mul2x32_0123_ac(k0,h4,_2a0)		;//# 2 b4 a1;
  mul2x32_0123_ac(k1,h0,a0)		;//#   b0 a1;
  mul2x32_2323_ac(k2,h0,_2a0)		;//# 2 b1 a1;
  mul2x32_0123_ac(k3,h2,a0)		;//#   b2 a1;
  mul2x32_2323_ac(k4,h2,_2a0)		;//# 2 b3 a1;

  mul2x32_2301_ac(k0,h2,_2a1)		;//# 2 b3 a2;
  mul2x32_0101_ac(k1,h4,a1)		;//#   b4 a2;
  mul2x32_0101_ac(k2,h0,a1)		;//#   b0 a2;
  mul2x32_2301_ac(k3,h0,a1)		;//#   b1 a2;
  mul2x32_0101_ac(k4,h2,a1)		;//#   b2 a2;
  
  mul2x32_0123_ac(k0,h2,_2a1)		;//# 2 b2 a3;
  mul2x32_2323_ac(k1,h2,_2a1)		;//# 2 b3 a3;
  mul2x32_0123_ac(k2,h4,_2a1)		;//# 2 b4 a3;
  mul2x32_0123_ac(k3,h0,a1)		;//#   b0 a3;
  mul2x32_2323_ac(k4,h0,_2a1)		;//# 2 b1 a3;

  mul2x32_2301_ac(k0,h0,_2a2)		;//# 2 b1 a4;
  mul2x32_0101_ac(k1,h2,a2)		;//#   b2 a4;
  mul2x32_2301_ac(k2,h2,_2a2)		;//# 2 b3 a4;
  mul2x32_0101_ac(k3,h4,a2)		;//#   b4 a4;
  mul2x32_0101_ac(k4,h0,a2)		;//#   b0 a4;


  //# carry; //#;
  
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);

  store128((mem128)ptr1,k0); ptr1+=16	;//# s + 32;
  store128((mem128)ptr1,k2); ptr1+=16	;//# s + 48;
  store128((mem128)ptr1,k4); ptr1+=16	;//# s + 64;

  //## sqr : x6; //##;

  shiftl2x(_2k0,k0,1);
  shiftl2x(_2k2,k2,1);
  shiftl2x(_2k4,k4,1);

  mul2x32_0101(h0,k0,k0)		;//#   a0 a0;
  mul2x32_2323(h2,_2k0,k0)		;//# 2 a1 a1;
  mul2x32_0101(h4,k2,k2)		;//#   a2 a2;
  mul2x32_2323(h1,_2k2,k2)		;//# 2 a3 a3;
  mul2x32_0101(h3,k4,k4)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2k0,k0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2k2,k0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2k2,k0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2k4,k0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2k4,_2k0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2k2,_2k0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2k2,k0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2k2,_2k2)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2k4,k2)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2k4,_2k2)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;
  
  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  //## sqr : x12; //##;
  
  shiftl2x(_2h0,h0,1);
  shiftl2x(_2h2,h2,1);
  shiftl2x(_2h4,h4,1);

  mul2x32_0101(k0,h0,h0)		;//#   a0 a0;
  mul2x32_2323(k2,_2h0,h0)		;//# 2 a1 a1;
  mul2x32_0101(k4,h2,h2)		;//#   a2 a2;
  mul2x32_2323(k1,_2h2,h2)		;//# 2 a3 a3;
  mul2x32_0101(k3,h4,h4)		;//#   a4 a4;

  mul2x32_2301_ac(k1,_2h0,h0)		;//# 2 a1 a0;
  mul2x32_0101_ac(k2,_2h2,h0)		;//# 2 a2 a0;
  mul2x32_2301_ac(k3,_2h2,h0)		;//# 2 a3 a0;
  mul2x32_0101_ac(k4,_2h4,h0)		;//# 2 a4 a0;

  mul2x32_0123_ac(k0,_2h4,_2h0)		;//# 4 a4 a1;
  mul2x32_2323_ac(k4,_2h2,_2h0)		;//# 4 a3 a1;
  mul2x32_0123_ac(k3,_2h2,h0)		;//# 2 a2 a1;

  mul2x32_2301_ac(k0,_2h2,_2h2)		;//# 4 a3 a2;
  mul2x32_0101_ac(k1,_2h4,h2)		;//# 2 a4 a2;
  
  mul2x32_0123_ac(k2,_2h4,_2h2)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  //# arrange; //#;
  
  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);

  //## mul : x15; //##;

  ptr1 -= 48				;//# s + 16;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 32;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 48;
  load128(a2,(mem128)ptr1); ptr1+=16	;//# s + 64;
  
  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);
  
  mul2x32_0101(h0,k0,a0)		;//#   b0 a0;
  mul2x32_2301(h1,k0,a0)		;//#   b1 a0;
  mul2x32_0101(h2,k2,a0)		;//#   b2 a0;
  mul2x32_2301(h3,k2,a0)		;//#   b3 a0;
  mul2x32_0101(h4,k4,a0)		;//#   b4 a0;

  mul2x32_0123_ac(h0,k4,_2a0)		;//# 2 b4 a1;
  mul2x32_0123_ac(h1,k0,a0)		;//#   b0 a1;
  mul2x32_2323_ac(h2,k0,_2a0)		;//# 2 b1 a1;
  mul2x32_0123_ac(h3,k2,a0)		;//#   b2 a1;
  mul2x32_2323_ac(h4,k2,_2a0)		;//# 2 b3 a1;

  mul2x32_2301_ac(h0,k2,_2a1)		;//# 2 b3 a2;
  mul2x32_0101_ac(h1,k4,a1)		;//#   b4 a2;
  mul2x32_0101_ac(h2,k0,a1)		;//#   b0 a2;
  mul2x32_2301_ac(h3,k0,a1)		;//#   b1 a2;
  mul2x32_0101_ac(h4,k2,a1)		;//#   b2 a2;

  mul2x32_0123_ac(h0,k2,_2a1)		;//# 2 b2 a3;
  mul2x32_2323_ac(h1,k2,_2a1)		;//# 2 b3 a3;
  mul2x32_0123_ac(h2,k4,_2a1)		;//# 2 b4 a3;
  mul2x32_0123_ac(h3,k0,a1)		;//#   b0 a3;
  mul2x32_2323_ac(h4,k0,_2a1)		;//# 2 b1 a3;

  mul2x32_2301_ac(h0,k0,_2a2)		;//# 2 b1 a4;
  mul2x32_0101_ac(h1,k2,a2)		;//#   b2 a4;
  mul2x32_2301_ac(h2,k2,_2a2)		;//# 2 b3 a4;
  mul2x32_0101_ac(h3,k4,a2)		;//#   b4 a4;
  mul2x32_0101_ac(h4,k0,a2)		;//#   b0 a4;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);
  
  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  //## sqr : x30; //##;

  shiftl2x(_2h0,h0,1);
  shiftl2x(_2h2,h2,1);
  shiftl2x(_2h4,h4,1);
  
  mul2x32_0101(k0,h0,h0)		;//#   a0 a0;
  mul2x32_2323(k2,_2h0,h0)		;//# 2 a1 a1;
  mul2x32_0101(k4,h2,h2)		;//#   a2 a2;
  mul2x32_2323(k1,_2h2,h2)		;//# 2 a3 a3;
  mul2x32_0101(k3,h4,h4)		;//#   a4 a4;

  mul2x32_2301_ac(k1,_2h0,h0)		;//# 2 a1 a0;
  mul2x32_0101_ac(k2,_2h2,h0)		;//# 2 a2 a0;
  mul2x32_2301_ac(k3,_2h2,h0)		;//# 2 a3 a0;
  mul2x32_0101_ac(k4,_2h4,h0)		;//# 2 a4 a0;

  mul2x32_0123_ac(k0,_2h4,_2h0)		;//# 4 a4 a1;
  mul2x32_2323_ac(k4,_2h2,_2h0)		;//# 4 a3 a1;
  mul2x32_0123_ac(k3,_2h2,h0)		;//# 2 a2 a1;
  
  mul2x32_2301_ac(k0,_2h2,_2h2)		;//# 4 a3 a2;
  mul2x32_0101_ac(k1,_2h4,h2)		;//# 2 a4 a2;
  
  mul2x32_0123_ac(k2,_2h4,_2h2)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);

  //## mul : x2^5-1; //##;

  adr1 = input_1;
  load128(a0,(mem128)adr1); adr1+=16;
  load128(a1,(mem128)adr1); adr1+=16;
  load128(a2,(mem128)adr1); adr1+=16;
  
  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,k0,a0)		;//#   b0 a0;
  mul2x32_2301(h1,k0,a0)		;//#   b1 a0;
  mul2x32_0101(h2,k2,a0)		;//#   b2 a0;
  mul2x32_2301(h3,k2,a0)		;//#   b3 a0;
  mul2x32_0101(h4,k4,a0)		;//#   b4 a0;

  mul2x32_0123_ac(h0,k4,_2a0)		;//# 2 b4 a1;
  mul2x32_0123_ac(h1,k0,a0)		;//#   b0 a1;
  mul2x32_2323_ac(h2,k0,_2a0)		;//# 2 b1 a1;
  mul2x32_0123_ac(h3,k2,a0)		;//#   b2 a1;
  mul2x32_2323_ac(h4,k2,_2a0)		;//# 2 b3 a1;

  mul2x32_2301_ac(h0,k2,_2a1)		;//# 2 b3 a2;
  mul2x32_0101_ac(h1,k4,a1)		;//#   b4 a2;
  mul2x32_0101_ac(h2,k0,a1)		;//#   b0 a2;
  mul2x32_2301_ac(h3,k0,a1)		;//#   b1 a2;
  mul2x32_0101_ac(h4,k2,a1)		;//#   b2 a2;

  mul2x32_0123_ac(h0,k2,_2a1)		;//# 2 b2 a3;
  mul2x32_2323_ac(h1,k2,_2a1)		;//# 2 b3 a3;
  mul2x32_0123_ac(h2,k4,_2a1)		;//# 2 b4 a3;
  mul2x32_0123_ac(h3,k0,a1)		;//#   b0 a3;
  mul2x32_2323_ac(h4,k0,_2a1)		;//# 2 b1 a3;

  mul2x32_2301_ac(h0,k0,_2a2)		;//# 2 b1 a4;
  mul2x32_0101_ac(h1,k2,a2)		;//#   b2 a4;
  mul2x32_2301_ac(h2,k2,_2a2)		;//# 2 b3 a4;
  mul2x32_0101_ac(h3,k4,a2)		;//#   b4 a4;
  mul2x32_0101_ac(h4,k0,a2)		;//#   b0 a4;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  ptr1 -= 48				;//# s + 16;
  store128((mem128)ptr1,h0); ptr1+=16	;//# s + 32	save x3;
  store128((mem128)ptr1,h2); ptr1+=16	;//# s + 48	save x3;
  store128((mem128)ptr1,h4); ptr1+=16	;//# s + 64	save x3;

  
  //##-----;//##;
  //#adr0 = input_0;
  //#store128((mem128)adr0,h0); adr0+=16;
  //#store128((mem128)adr0,h2); adr0+=16;
  s4 = h4;
  //##-----;//##;
  
  //#/////////////////////////////////////////////////;
  
  //#=============;//#;
  //# Second Half; //#;
  //#=============;//#;
  
  adr1 = input_1 + 32;
  load128(a2,(mem128)adr1); adr1+=16;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  //## sqr :x2; //##;

  shiftl2x(_2a2,a2,1);
  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h4,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h4,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);
  //##-----;//##;



  //## mul : x3; //##;

  mul2x32_0101(k0,h0,a3)		;//#   b0 a0;
  mul2x32_2301(k1,h0,a3)		;//#   b1 a0;
  mul2x32_0101(k2,h2,a3)		;//#   b2 a0;
  mul2x32_2301(k3,h2,a3)		;//#   b3 a0;
  mul2x32_0101(k4,h4,a3)		;//#   b4 a0;

  mul2x32_0123_ac(k0,h4,_2a3)		;//# 2 b4 a1;
  mul2x32_0123_ac(k1,h0,a3)		;//#   b0 a1;
  mul2x32_2323_ac(k2,h0,_2a3)		;//# 2 b1 a1;
  mul2x32_0123_ac(k3,h2,a3)		;//#   b2 a1;
  mul2x32_2323_ac(k4,h2,_2a3)		;//# 2 b3 a1;

  mul2x32_2301_ac(k0,h2,_2a4)		;//# 2 b3 a2;
  mul2x32_0101_ac(k1,h4,a4)		;//#   b4 a2;
  mul2x32_0101_ac(k2,h0,a4)		;//#   b0 a2;
  mul2x32_2301_ac(k3,h0,a4)		;//#   b1 a2;
  mul2x32_0101_ac(k4,h2,a4)		;//#   b2 a2;

  mul2x32_0123_ac(k0,h2,_2a4)		;//# 2 b2 a3;
  mul2x32_2323_ac(k1,h2,_2a4)		;//# 2 b3 a3;
  mul2x32_0123_ac(k2,h4,_2a4)		;//# 2 b4 a3;
  mul2x32_0123_ac(k3,h0,a4)		;//#   b0 a3;
  mul2x32_2323_ac(k4,h0,_2a4)		;//# 2 b1 a3;

  mul2x32_2323_ac(k0,h0,_2a2)		;//# 2 b1 a4;
  mul2x32_0123_ac(k1,h2,a2)		;//#   b2 a4;
  mul2x32_2323_ac(k2,h2,_2a2)		;//# 2 b3 a4;
  mul2x32_0123_ac(k3,h4,a2)		;//#   b4 a4;
  mul2x32_0123_ac(k4,h0,a2)		;//#   b0 a4;


  //# carry; //#;

  ptr1 -= 64			;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);

  ptr1 += 96				;//# s + 96;
  store128((mem128)ptr1,k0); ptr1+=16	;//# s + 112;
  store128((mem128)ptr1,k2); ptr1+=16	;//# s + 128;
  ptr1 -= 80				;//# s + 48;
  load128(k1,(mem128)ptr1);
  set_lane_64_0010(k1,k4);
  ptr1 += 80				;//# s + 128;
  store128((mem128)ptr1,k1);



  //## sqr : x6; //##;

  shiftl2x(_2k0,k0,1);
  shiftl2x(_2k2,k2,1);
  shiftl2x(_2k4,k4,1);

  mul2x32_0101(h0,k0,k0)		;//#   a0 a0;
  mul2x32_2323(h2,_2k0,k0)		;//# 2 a1 a1;
  mul2x32_0101(h4,k2,k2)		;//#   a2 a2;
  mul2x32_2323(h1,_2k2,k2)		;//# 2 a3 a3;
  mul2x32_0101(h3,k4,k4)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2k0,k0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2k2,k0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2k2,k0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2k4,k0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2k4,_2k0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2k2,_2k0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2k2,k0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2k2,_2k2)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2k4,k2)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2k4,_2k2)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  //## sqr : x12; //##;

  shiftl2x(_2h0,h0,1);
  shiftl2x(_2h2,h2,1);
  shiftl2x(_2h4,h4,1);

  mul2x32_0101(k0,h0,h0)		;//#   a0 a0;
  mul2x32_2323(k2,_2h0,h0)		;//# 2 a1 a1;
  mul2x32_0101(k4,h2,h2)		;//#   a2 a2;
  mul2x32_2323(k1,_2h2,h2)		;//# 2 a3 a3;
  mul2x32_0101(k3,h4,h4)		;//#   a4 a4;

  mul2x32_2301_ac(k1,_2h0,h0)		;//# 2 a1 a0;
  mul2x32_0101_ac(k2,_2h2,h0)		;//# 2 a2 a0;
  mul2x32_2301_ac(k3,_2h2,h0)		;//# 2 a3 a0;
  mul2x32_0101_ac(k4,_2h4,h0)		;//# 2 a4 a0;

  mul2x32_0123_ac(k0,_2h4,_2h0)		;//# 4 a4 a1;
  mul2x32_2323_ac(k4,_2h2,_2h0)		;//# 4 a3 a1;
  mul2x32_0123_ac(k3,_2h2,h0)		;//# 2 a2 a1;

  mul2x32_2301_ac(k0,_2h2,_2h2)		;//# 4 a3 a2;
  mul2x32_0101_ac(k1,_2h4,h2)		;//# 2 a4 a2;

  mul2x32_0123_ac(k2,_2h4,_2h2)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);


  //# arrange; //#;

  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);



  //## mul : x15; //##;

  //#ptr1 -= 96				;//# s + 64;
  ;//# s + 128;
  load128(a2,(mem128)ptr1);
  ptr1 -= 32				;//# s + 96;
  load128(a3,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(a4,(mem128)ptr1); ptr1+=16	;//# s + 128;


  shiftl2x(_2a2,a2,1);
  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,k0,a3)		;//#   b0 a0;
  mul2x32_2301(h1,k0,a3)		;//#   b1 a0;
  mul2x32_0101(h2,k2,a3)		;//#   b2 a0;
  mul2x32_2301(h3,k2,a3)		;//#   b3 a0;
  mul2x32_0101(h4,k4,a3)		;//#   b4 a0;

  mul2x32_0123_ac(h0,k4,_2a3)		;//# 2 b4 a1;
  mul2x32_0123_ac(h1,k0,a3)		;//#   b0 a1;
  mul2x32_2323_ac(h2,k0,_2a3)		;//# 2 b1 a1;
  mul2x32_0123_ac(h3,k2,a3)		;//#   b2 a1;
  mul2x32_2323_ac(h4,k2,_2a3)		;//# 2 b3 a1;

  mul2x32_2301_ac(h0,k2,_2a4)		;//# 2 b3 a2;
  mul2x32_0101_ac(h1,k4,a4)		;//#   b4 a2;
  mul2x32_0101_ac(h2,k0,a4)		;//#   b0 a2;
  mul2x32_2301_ac(h3,k0,a4)		;//#   b1 a2;
  mul2x32_0101_ac(h4,k2,a4)		;//#   b2 a2;

  mul2x32_0123_ac(h0,k2,_2a4)		;//# 2 b2 a3;
  mul2x32_2323_ac(h1,k2,_2a4)		;//# 2 b3 a3;
  mul2x32_0123_ac(h2,k4,_2a4)		;//# 2 b4 a3;
  mul2x32_0123_ac(h3,k0,a4)		;//#   b0 a3;
  mul2x32_2323_ac(h4,k0,_2a4)		;//# 2 b1 a3;

  mul2x32_2323_ac(h0,k0,_2a2)		;//# 2 b1 a4;
  mul2x32_0123_ac(h1,k2,a2)		;//#   b2 a4;
  mul2x32_2323_ac(h2,k2,_2a2)		;//# 2 b3 a4;
  mul2x32_0123_ac(h3,k4,a2)		;//#   b4 a4;
  mul2x32_0123_ac(h4,k0,a2)		;//#   b0 a4;


  //# carry; //#;

  ptr1 -= 128			;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);



  //## sqr : x30; //##;

  shiftl2x(_2h0,h0,1);
  shiftl2x(_2h2,h2,1);
  shiftl2x(_2h4,h4,1);

  mul2x32_0101(k0,h0,h0)		;//#   a0 a0;
  mul2x32_2323(k2,_2h0,h0)		;//# 2 a1 a1;
  mul2x32_0101(k4,h2,h2)		;//#   a2 a2;
  mul2x32_2323(k1,_2h2,h2)		;//# 2 a3 a3;
  mul2x32_0101(k3,h4,h4)		;//#   a4 a4;

  mul2x32_2301_ac(k1,_2h0,h0)		;//# 2 a1 a0;
  mul2x32_0101_ac(k2,_2h2,h0)		;//# 2 a2 a0;
  mul2x32_2301_ac(k3,_2h2,h0)		;//# 2 a3 a0;
  mul2x32_0101_ac(k4,_2h4,h0)		;//# 2 a4 a0;

  mul2x32_0123_ac(k0,_2h4,_2h0)		;//# 4 a4 a1;
  mul2x32_2323_ac(k4,_2h2,_2h0)		;//# 4 a3 a1;
  mul2x32_0123_ac(k3,_2h2,h0)		;//# 2 a2 a1;

  mul2x32_2301_ac(k0,_2h2,_2h2)		;//# 4 a3 a2;
  mul2x32_0101_ac(k1,_2h4,h2)		;//# 2 a4 a2;

  mul2x32_0123_ac(k2,_2h4,_2h2)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  shiftur2x(t,k1,25);
  add2x(k2,k2,t);
  and128(k1, k1, mask25);

  shiftur2x(t,k2,26);
  add2x(k3,k3,t);
  and128(k2, k2, mask26);

  shiftur2x(t,k3,25);
  add2x(k4,k4,t);
  and128(k3, k3, mask25);

  shiftur2x(t,k4,25);
  add2x(k0,k0,t);
  and128(k4, k4, mask25);
  //#--;
  shiftur2x(t,k0,26);
  add2x(k1,k1,t);
  and128(k0, k0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(k0,k1);
  permute32_0213(k0);
  mix32_00100212_01110313(k2,k3);
  permute32_0213(k2);
  permute32_0213(k4);



  //## mul : x2^5-1; //##;

  adr1 = input_1 + 32;
  load128(a2,(mem128)adr1); adr1+=16;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a2,a2,1);
  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,k0,a3)		;//#   b0 a0;
  mul2x32_2301(h1,k0,a3)		;//#   b1 a0;
  mul2x32_0101(h2,k2,a3)		;//#   b2 a0;
  mul2x32_2301(h3,k2,a3)		;//#   b3 a0;
  mul2x32_0101(h4,k4,a3)		;//#   b4 a0;

  mul2x32_0123_ac(h0,k4,_2a3)		;//# 2 b4 a1;
  mul2x32_0123_ac(h1,k0,a3)		;//#   b0 a1;
  mul2x32_2323_ac(h2,k0,_2a3)		;//# 2 b1 a1;
  mul2x32_0123_ac(h3,k2,a3)		;//#   b2 a1;
  mul2x32_2323_ac(h4,k2,_2a3)		;//# 2 b3 a1;

  mul2x32_2301_ac(h0,k2,_2a4)		;//# 2 b3 a2;
  mul2x32_0101_ac(h1,k4,a4)		;//#   b4 a2;
  mul2x32_0101_ac(h2,k0,a4)		;//#   b0 a2;
  mul2x32_2301_ac(h3,k0,a4)		;//#   b1 a2;
  mul2x32_0101_ac(h4,k2,a4)		;//#   b2 a2;

  mul2x32_0123_ac(h0,k2,_2a4)		;//# 2 b2 a3;
  mul2x32_2323_ac(h1,k2,_2a4)		;//# 2 b3 a3;
  mul2x32_0123_ac(h2,k4,_2a4)		;//# 2 b4 a3;
  mul2x32_0123_ac(h3,k0,a4)		;//#   b0 a3;
  mul2x32_2323_ac(h4,k0,_2a4)		;//# 2 b1 a3;

  mul2x32_2323_ac(h0,k0,_2a2)		;//# 2 b1 a4;
  mul2x32_0123_ac(h1,k2,a2)		;//#   b2 a4;
  mul2x32_2323_ac(h2,k2,_2a2)		;//# 2 b3 a4;
  mul2x32_0123_ac(h3,k4,a2)		;//#   b4 a4;
  mul2x32_0123_ac(h4,k0,a2)		;//#   b0 a4;


  //# carry; //#;

  load128(mask25,(mem128)ptr1);

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  set_lane_64_0010(s4,h4);
  ptr1 += 48				;//# s + 48;
  store128((mem128)ptr1,s4); ptr1+=16	;//# s + 64	save x3;
  store128((mem128)ptr1,h0); ptr1+=16	;//# s + 80	save x3;
  store128((mem128)ptr1,h2); ptr1+=16	;//# s + 96	save x3;

  //##-----;//##;
  //#adr0 = input_0 + 32;
  //#store128((mem128)adr0,s4); adr0+=16;
  //#store128((mem128)adr0,h0); adr0+=16;
  //#store128((mem128)adr0,h2); adr0+=16;
  //##-----;//##;

  //###################################################################################################;

  //##;

  //###############;
  //# sqrx5   mul; //#;
  //###############;

  ptr1 -= 80				;//# s + 16;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 32;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 48;
  a2 = s4;
  a3 = h0;
  a4 = h2;


  //## First half; //##;

  ctr = 5;

 loop5:

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);


  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;


  //####;


  //## Second half; //##;


  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);


  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);


  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);


  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop5;


  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;


  //###################################################################################################;


  ptr1 -= 32				;//# s + 16;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 32;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 48;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 64;


  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);




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

  ptr1 -= 64					;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 96				;//# s + 96;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 112;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 128;


  //####;


  //## Second half; //##;

  adr1 = input_0 +48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  ptr1 -= 64				;//# s + 64;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 80;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 96;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

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


  ptr1 -= 96					;//# s + 0;
  load128(mask25,(mem128)ptr1);

  //# carry; //#;

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 128				;//# s + 128;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 144;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 160;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 176;


  //###################################################################################################;


  //################;
  //# sqrx10   mul; //#;
  //################;

  ptr1 -= 80				;//# s + 96;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  a2 = r4;
  a3 = r0;
  a4 = r2;


  //## First half; //##;

  ctr = 10;

 loop10:
  //#a0 = h0;
  //#a1 = h2;
  //#a2 = h4;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;


  //####;


  //## Second half; //##;


  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);


  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);


  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);


  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop10;


  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;



  //###################################################################################################;


  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);


  ptr1 -= 32				;//# s + 96;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 144;


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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);


  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 32				;//# s + 176;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 192;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 208;



  //####;


  //## Second half; //##;


  adr1 = input_0 + 48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);


  ptr1 -= 64				;//# s + 144;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 160;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 176;

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

  ptr1 -= 176				;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 208				;//# s + 208;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 224;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 240;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 256;

  //###################################################################################################;

  //################;
  //# sqrx20   mul; //#;
  //################;

  ptr1 -= 80				;//# s + 176;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 192;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 208;
  a2 = r4;
  a3 = r0;
  a4 = r2;

  //## First half; //##;

  ctr = 20;

 loop20:

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  //####;

  //## Second half; //##;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);


  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop20;

  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;

  //###################################################################################################;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  ptr1 -= 32				;//# s + 176;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 192;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 208;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 224;


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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 -= 128				;//# s + 96;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 112;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 128;

  //####;

  //## Second half; //##;

  adr1 = input_0 + 48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  ptr1 += 96				;//# s + 224;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 240;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 256;


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

  ptr1 -= 256			;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 128				;//# s + 128;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 144;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 160;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 176;

  //###################################################################################################;

  //################;
  //# sqrx40   mul; //#;
  //################;

  ptr1 -= 80				;//# s + 96;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  a2 = r4;
  a3 = r0;
  a4 = r2;

  //## First half; //##;

  ctr = 40;

 loop40:

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3 , h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  //####;

  //## Second half; //##;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);

  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop40;

  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;

  //###################################################################################################;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  ptr1 -= 32				;//# s + 96;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 144;

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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 32				;//# s + 176;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 192;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 208;

  //####;

  //## Second half; //##;

  adr1 = input_0 + 48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  ptr1 -= 64				;//# s + 144;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 160;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 176;

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

  ptr1 -= 176				;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 208				;//# s + 208;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 224;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 240;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 256;

  //###################################################################################################;

  //################################;
  //# sqrx40   mul   -->   x_120_0; //#;
  //################################;

  ptr1 -= 80				;//# s + 176;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 192;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 208;
  a2 = r4;
  a3 = r0;
  a4 = r2;

  //## First half; //##;

  ctr = 40;

 loop40_:

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  //####;

  //## Second half; //##;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);

  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop40_;

  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;

  //###################################################################################################;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  ptr1 -= 112				;//# s + 96;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 144;

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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 112				;//# s + 256;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 272;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 288;

  //####;

  //## Second half; //##;

  adr1 = input_0 + 48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  ptr1 -= 144				;//# s + 144;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 160;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 176;

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

  ptr1 -= 176				;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 288				;//# s + 288;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 304;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 320;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 336;

  //###################################################################################################;

  ptr1 -= 80				;//# s + 256;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 272;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 288;
  a2 = r4;
  a3 = r0;
  a4 = r2;

  //## First half; //##;

  ctr = 5;

 loop5_:

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  mul2x32_0101(h0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(h2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(h4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(h1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(h4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(h0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(h4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(h1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(h2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h4,h4,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h4,25);
  add2x(h0,h0,t);
  and128(h4, h4, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);
  permute32_0213(h4);

  a0 = h0;
  a1 = h2;
  set_lane_64_1001(a2,h4);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  //####;

  //## Second half; //##;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(h0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(h2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(h5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(h1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(h3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(h1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(h2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(h3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(h5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(h0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(h5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(h3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(h0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(h1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(h2,_2a2,_2a4)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  shiftur2x(t,h1,25);
  add2x(h2,h2,t);
  and128(h1, h1, mask25);

  shiftur2x(t,h2,26);
  add2x(h3,h3,t);
  and128(h2, h2, mask26);

  shiftur2x(t,h3,25);
  add2x(h5,h5,t);
  and128(h3, h3, mask25);

  shiftur2x(t,h5,25);
  add2x(h0,h0,t);
  and128(h5, h5, mask25);
  //#--;
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(h0,h1);
  permute32_0213(h0);
  mix32_00100212_01110313(h2,h3);
  permute32_0213(h2);

  //#mix32_00100212_01110313(h4,h5);
  permute32_0213(h5);

  a3 = h0;
  a4 = h2;
  set_lane_64_0010(a2,h5);

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ctr -= 1;
  if (ctr > 0)
    goto loop5_;

  adr0 = input_0 + 48;
  //#store128((mem128)adr0,a0); adr0+=16;
  //#store128((mem128)adr0,a1); adr0+=16;
  //#store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;

  //###################################################################################################;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  ptr1 -= 272				;//# s + 16;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 32;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 48;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 64;

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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 112				;//# s + 176;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 192;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 208;

  //####;

  //## Second half; //##;

  adr1 = input_0 + 48;
  load128(a3,(mem128)adr1); adr1+=16;
  load128(a4,(mem128)adr1); adr1+=16;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  ptr1 -= 144				;//# s + 64;
  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 80;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 96;

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

  ptr1 -= 96				;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 208				;//# s + 208;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 224;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 240;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 256;

  //###################################################################################################;

  //#############;
  //# 2^127 - 3; //#;
  //#############;

  ptr1 -= 80				;//# s + 176;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 192;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 208;
  a2 = r4;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  //## First half; //##;

  mul2x32_0101(r0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(r2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(r4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(r1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(r3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(r1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(r2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(r3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(r4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(r0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(r4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(r3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(r0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(r1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(r2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 -=192				;//# s + 16;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 32;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 48;

  //####;

  //## Second half; //##;

  ptr1 += 176				;//# s + 224;
  load128(a3,(mem128)ptr1); ptr1+=16	;//# s + 240;
  load128(a4,(mem128)ptr1); ptr1+=16	;//# s + 256;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(r0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(r2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(r5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(r1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(r3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(r1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(r2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(r3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(r5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(r0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(r5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(r3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(r0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(r1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(r2,_2a2,_2a4)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 -= 208				;//# s + 48;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 64;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 80;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 96;

  //###################################################################################################;

  ptr1 -= 80				;//# s + 16;
  load128(a0,(mem128)ptr1); ptr1+=16	;//# s + 32;
  load128(a1,(mem128)ptr1); ptr1+=16	;//# s + 48;
  load128(a2,(mem128)ptr1); ptr1+=16	;//# s + 64;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  //## First half; //##;

  mul2x32_0101(r0,a0,a0)		;//#   a0 a0;
  mul2x32_2323(r2,_2a0,a0)		;//# 2 a1 a1;
  mul2x32_0101(r4,a1,a1)		;//#   a2 a2;
  mul2x32_2323(r1,_2a1,a1)		;//# 2 a3 a3;
  mul2x32_0101(r3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(r1,_2a0,a0)		;//# 2 a1 a0;
  mul2x32_0101_ac(r2,_2a1,a0)		;//# 2 a2 a0;
  mul2x32_2301_ac(r3,_2a1,a0)		;//# 2 a3 a0;
  mul2x32_0101_ac(r4,_2a2,a0)		;//# 2 a4 a0;

  mul2x32_0123_ac(r0,_2a2,_2a0)		;//# 4 a4 a1;
  mul2x32_2323_ac(r4,_2a1,_2a0)		;//# 4 a3 a1;
  mul2x32_0123_ac(r3,_2a1,a0)		;//# 2 a2 a1;

  mul2x32_2301_ac(r0,_2a1,_2a1)		;//# 4 a3 a2;
  mul2x32_0101_ac(r1,_2a2,a1)		;//# 2 a4 a2;

  mul2x32_0123_ac(r2,_2a2,_2a1)		;//# 4 a4 a3;

  //# carry; //#;

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  //#adr0 = input_0;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 32				;//# s + 96;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 112;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 128;

  //####;

  //## Second half; //##;

  ptr1 -= 64				;//# s + 64;
  load128(a3,(mem128)ptr1); ptr1+=16	;//# s + 80;
  load128(a4,(mem128)ptr1); ptr1+=16	;//# s + 96;

  shiftl2x(_2a3,a3,1);
  shiftl2x(_2a4,a4,1);

  mul2x32_0101(r0,a3,a3)		;//#   a0 a0;
  mul2x32_2323(r2,_2a3,a3)		;//# 2 a1 a1;
  mul2x32_0101(r5,a4,a4)		;//#   a2 a2;
  mul2x32_2323(r1,_2a4,a4)		;//# 2 a3 a3;
  mul2x32_2323(r3,a2,a2)		;//#   a4 a4;

  mul2x32_2301_ac(r1,_2a3,a3)		;//# 2 a1 a0;
  mul2x32_0101_ac(r2,_2a4,a3)		;//# 2 a2 a0;
  mul2x32_2301_ac(r3,_2a4,a3)		;//# 2 a3 a0;
  mul2x32_2301_ac(r5,_2a2,a3)		;//# 2 a4 a0;

  mul2x32_2323_ac(r0,_2a2,_2a3)		;//# 4 a4 a1;
  mul2x32_2323_ac(r5,_2a4,_2a3)		;//# 4 a3 a1;
  mul2x32_0123_ac(r3,_2a4,a3)		;//# 2 a2 a1;

  mul2x32_2301_ac(r0,_2a4,_2a4)		;//# 4 a3 a2;
  mul2x32_2301_ac(r1,_2a2,a4)		;//# 2 a4 a2;

  mul2x32_2323_ac(r2,_2a2,_2a4)		;//# 4 a4 a3;


  //# carry; //#;

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  //# arrange; //#;

  mix32_00100212_01110313(r0,r1);
  permute32_0213(r0);
  mix32_00100212_01110313(r2,r3);
  permute32_0213(r2);

  mix32_00100212_01110313(r4,r5);
  permute32_0213(r4);

  //####;

  //#store128((mem128)adr0,r4); adr0+=16;
  //#store128((mem128)adr0,r0); adr0+=16;
  //#store128((mem128)adr0,r2); adr0+=16;

  ptr1 += 32				;//# s + 128;
  store128((mem128)ptr1,r4); ptr1+=16	;//# s + 144;
  store128((mem128)ptr1,r0); ptr1+=16	;//# s + 160;
  store128((mem128)ptr1,r2); ptr1+=16	;//# s + 176;

  //###################################################################################################;

  adr1 = input_1;
  load128(a0,(mem128)adr1); adr1+=16;
  load128(a1,(mem128)adr1); adr1+=16;
  load128(a2,(mem128)adr1); adr1+=16;

  shiftl2x(_2a0,a0,1);
  shiftl2x(_2a1,a1,1);
  shiftl2x(_2a2,a2,1);

  ptr1 -= 80				;//# s + 96;
  load128(b0,(mem128)ptr1); ptr1+=16	;//# s + 112;
  load128(b1,(mem128)ptr1); ptr1+=16	;//# s + 128;
  load128(b2,(mem128)ptr1); ptr1+=16	;//# s + 144;

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
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r4,r4,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r4,25);
  add2x(r0,r0,t);
  and128(r4, r4, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

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

  load128(b3,(mem128)ptr1); ptr1+=16	;//# s + 160;
  load128(b4,(mem128)ptr1); ptr1+=16	;//# s + 176;

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

  ptr1 -= 176			;//# s + 0;
  load128(mask25,(mem128)ptr1);

  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

  shiftur2x(t,r1,25);
  add2x(r2,r2,t);
  and128(r1, r1, mask25);

  shiftur2x(t,r2,26);
  add2x(r3,r3,t);
  and128(r2, r2, mask26);

  shiftur2x(t,r3,25);
  add2x(r5,r5,t);
  and128(r3, r3, mask25);

  shiftur2x(t,r5,25);
  add2x(r0,r0,t);
  and128(r5, r5, mask25);
  //#--;
  shiftur2x(t,r0,26);
  add2x(r1,r1,t);
  and128(r0, r0, mask26);

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

  //#;

  //###################################################################################################;

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
