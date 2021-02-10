#include <stdio.h>
#include "myneon.h"

void invert(address input_0, address input_1);

typedef struct{
  int32 v[20]; 
  /* x20 y20 x21 y21 , x22 y22 x23 y23 , x24 y24 z34 t34 , z30 t30 z31 t31 , z32 t32 z33 t33 */
} gfex4;

int main(void) {
    gfex4 e1e2e3e4 = { { 56813937, 47364535, 30483653, 3246959, 23197289, 20145721,
                         24199848, 5019917, 20583030, 30978035, 25603526, 31096441,
                         23098912, 18633942, 5850941, 16266296, 24284645, 46390456,
                         24506596, 11091040 } };

    gfex4 inv = { { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 } };
    
    invert((address)&inv,(address)&e1e2e3e4);

    printf("Inverse1: (%x,%x,%x,%x,%x)\nInverse2: (%x,%x,%x,%x,%x)\nInverse3: (%x,%x,%x,%x,%x)\nInverse4: (%x,%x,%x,%x,%x)\n",
                inv.v[0],inv.v[2],inv.v[4],inv.v[6],inv.v[8],
                inv.v[1],inv.v[3],inv.v[5],inv.v[7],inv.v[9],
                inv.v[12],inv.v[14],inv.v[16],inv.v[18],inv.v[10],
                inv.v[13],inv.v[15],inv.v[17],inv.v[19],inv.v[11]);

    return 0;
}
