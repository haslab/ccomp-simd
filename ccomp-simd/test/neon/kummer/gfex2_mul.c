#include "myneon.h"

void gfex2_mul(address input_0, address input_1, address input_2) {
  int128 f0, f1, f2;
  int128 _2f1, _2f2;
  int128 g0, g1, g2;
  int128 h0, h1, h2, h3, h4;
  int128 t, mask25, mask26;
  address adr0, adr1, adr2;
  int32 count;

  /*
    stack128 caller_q4_stack
    stack128 caller_q5_stack
    stack128 caller_q6_stack
    stack128 caller_q7_stack
    
    qpushenter gfex2_mul
  */

  adr0 = input_0;
  adr1 = input_1;
  adr2 = input_2;
  
  set2x(mask25,0xffffffff);
  shiftl4x_in(mask25,7);
  shiftur2x_in(mask25,7);
  
  set2x(mask26,0xffffffff);
  shiftl4x_in(mask26,6);
  shiftur2x_in(mask26,6);

  //####;

  load128(f0,(mem128)adr1);
  adr1+=8;
  load128(f1,(mem128)adr1); adr1+=16;
  load128(f2,(mem128)adr1); adr1+=16;
  
  shiftl2x(_2f1,f1,1);
  shiftl2x(_2f2,f2,1);

  load128(g0,(mem128)adr2);
  adr2+=8;
  load128(g1,(mem128)adr2); adr2+=16;
  load128(g2,(mem128)adr2); adr2+=16;
  
  //#count = 10000;
  //#loop:
  
  mul2x32_0101(h0,f0,g0);
  mul2x32_0101(h1,f1,g0);
  mul2x32_2301(h2,f1,g0);
  mul2x32_0101(h3,f2,g0);
  mul2x32_2301(h4,f2,g0);
  
  mul2x32_0123_ac(h0,_2f2,g1);
  mul2x32_2301_ac(h0,_2f2,g1);
  mul2x32_0101_ac(h1,f0,g1);
  mul2x32_2323_ac(h1,f2,g1);
  mul2x32_0123_ac(h2,f0,g1);
  mul2x32_0101_ac(h2,_2f1,g1);
  mul2x32_2301_ac(h3,f1,g1);
  mul2x32_0123_ac(h3,f1,g1);
  mul2x32_2323_ac(h4,f1,g1);
  mul2x32_0101_ac(h4,_2f2,g1);

  mul2x32_0123_ac(h0,_2f1,g2);
  mul2x32_2301_ac(h0,_2f1,g2);
  mul2x32_0101_ac(h1,_2f2,g2);
  mul2x32_2323_ac(h1,f1,g2);
  mul2x32_0123_ac(h2,_2f2,g2);
  mul2x32_2301_ac(h2,_2f2,g2);
  mul2x32_0101_ac(h3,f0,g2);
  mul2x32_2323_ac(h3,f2,g2);
  mul2x32_0123_ac(h4,f0,g2);
  mul2x32_0101_ac(h4,_2f1,g2);

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
  //#--
  shiftur2x(t,h0,26);
  add2x(h1,h1,t);
  and128(h0, h0, mask26);

  //#shiftur2x(t,h1,25);
  //#add2x(h2,h2,t);
  //#h1 &= mask25;

  //#shiftur2x(t,h2,26);
  //#add2x(h3,h3,t);
  //#h2 &= mask26;

  //#shiftur2x(t,h3,25);
  //#add2x(h4,h4,t);
  //#h3 &= mask25;

  //#shiftur2x(t,h4,25);
  //#add2x(h0,h0,t);
  //#h4 &= mask25;

  //# arrange; //#;
  permute32_0213(h0);
  mix32_00100212_01110313(h1,h2);
  permute32_0213(h1);
  
  mix32_00100212_01110313(h3,h4);
  permute32_0213(h3);

  //####;
  
  //#count -= 1;
  //#if (count > 0);
  //#goto loop;

  store128((mem128)adr0,h0);
  adr0+=8;
  store128((mem128)adr0,h1); adr0+=16;
  store128((mem128)adr0,h3); adr0+=16;
}
//qpopreturn;
