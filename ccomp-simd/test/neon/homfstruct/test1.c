int printf(char *s, ...);

typedef struct { double x; double y;} H;
typedef struct { double val[2];} H2;



H f (int x, H y) {
  H r;
  r.x = y.y + (double) x;
  r.y = y.x;
  return r;
}

H2 f2 (int x, H2 y) {
  H2 r;
  r.val[0] = y.val[0] + (double) x;
  r.val[1] = y.val[1];
  return r;
}

double h(double x, double y) {
  H r = {x,y};
  return 2.0;
}

int g() {
 H x;
 x.x = 1.1;
 x.y = 2.2;
 x = f(5,x);
 x.y = h(x.x,x.y);
 printf("%lf\n%lf\n", x.x, x.y);
 return 0;
}


