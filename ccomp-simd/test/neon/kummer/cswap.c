#include "myneon.h"

void cswap(address input_0, address input_1, int32 input_2) {
  int128 a0, a1, a2, a3, a4;
  int128 b0, b1, b2, b3, b4;
  int128 t, c;
  int32 bit;

  address adr0;
  address adr1;
  address adr2;

  int32 count;

  /*
    stack128 caller_q4_stack
    stack128 caller_q5_stack
    stack128 caller_q6_stack
    stack128 caller_q7_stack
    
    qpushenter cswap
    
    //count = 10000
    //loop:
    */

  adr0 = input_0;
  load128(a0,(mem128)adr0); adr0+=16;
  load128(a1,(mem128)adr0); adr0+=16;
  load128(a2,(mem128)adr0); adr0+=16;
  load128(a3,(mem128)adr0); adr0+=16;
  load128(a4,(mem128)adr0); adr0+=16;

  adr1 = input_1;
  load128(b0,(mem128)adr1); adr1+=16;
  load128(b1,(mem128)adr1); adr1+=16;
  load128(b2,(mem128)adr1); adr1+=16;
  load128(b3,(mem128)adr1); adr1+=16;
  load128(b4,(mem128)adr1); adr1+=16;


  //#adr2 = input_2;
  bit = input_2;

  bit -= 1;
  set4x(c,bit);

  xor128(t, a0, b0);
  and128(t, t, c);
  xor128(a0, a0, t);
  xor128(b0, b0, t);
  
  xor128(t, a1, b1);
  and128(t, t, c);
  xor128(a1, a1, t);
  xor128(b1, b1, t);

  xor128(t, a2, b2);
  and128(t, t, c);
  xor128(a2, a2, t);
  xor128(b2, b2, t);

  xor128(t, a3, b3);
  and128(t, t, c);
  xor128(a3, a3, t);
  xor128(b3, b3, t);

  xor128(t, a4, b4);
  and128(t, t, c);
  xor128(a4, a4, t);
  xor128(b4, b4, t);

  adr0 = input_0;
  store128((mem128)adr0,a0); adr0+=16;
  store128((mem128)adr0,a1); adr0+=16;
  store128((mem128)adr0,a2); adr0+=16;
  store128((mem128)adr0,a3); adr0+=16;
  store128((mem128)adr0,a4); adr0+=16;

  adr1 = input_1;
  store128((mem128)adr1,b0); adr1+=16;
  store128((mem128)adr1,b1); adr1+=16;
  store128((mem128)adr1,b2); adr1+=16;
  store128((mem128)adr1,b3); adr1+=16;
  store128((mem128)adr1,b4); adr1+=16;

  //#count -= 1;
  //#if (count > 0);
  //#goto loop;
}

//qpopreturn;

