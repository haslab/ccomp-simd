#define cpuid(func,ax,bx,cx,dx)			\
  __asm__ __volatile__ ("cpuid":					\
  "=a" (ax), "=b" (bx), "=c" (cx), "=d" (dx) : "a" (func));

int Check_CPU_support_AES() {
#if defined (__GCC__)
  unsigned int a,b,c,d;
  cpuid(1, a,b,c,d);
  return (c & 0x2000000);
#else
  return 1;
#endif
}


