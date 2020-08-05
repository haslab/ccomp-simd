/* code adapted from Intel's TimerUtility C++ class */
#include <stdint.h>
#include <sys/time.h>

typedef struct{
  // the start time and end time in seconds
  double m_start_time, m_end_time, acc_time; 
  // the start clock tick and end clock tick
  unsigned long long m_start_clock_tick, m_end_clock_tick, acc_tick;
  int cnt;
} timer_info;

#if defined (__GNUC__)
static inline uint64_t __rdtsc()
{
   uint32_t lo, hi;
   __asm__ __volatile__ (
                         "xorl %%eax, %%eax\n"
                         "cpuid\n"
                         "rdtsc\n"
                         : "=a" (lo), "=d" (hi)
                         :
                         : "%ebx", "%ecx" );
   return (uint64_t)hi << 32 | lo;
}
#elif defined (__COMPCERT__)
#define __rdtsc	__builtin_rdtsc
#endif

static inline void timer_init(timer_info *t) {
  t->cnt = 0;
  t->acc_time = 0;
  t->acc_tick = 0;
}

// Description:
// Registers the current clock tick value in m_start_clock_tick, current time value in m_start_time
// Uses the rdtsc instruction for clock ticks and get_timeofday for time
static inline void timer_start(timer_info *t) {
  // Clock ticks
  t->m_start_clock_tick = __rdtsc();
  // Time
  struct timeval start;
  gettimeofday(&start, 0); //Returns the time of the day
  //tv_sec records time in micro-seconds and tv_usec records time in micro seconds
  t->m_start_time = ((double) start.tv_sec * 1000.0) + (double) start.tv_usec / 1000.0; 
}

// Description:
// Registers the current clock tick value in m_end_clock_tick, current time value in m_end_time
// Uses the rdtsc instruction for clock ticks and get_timeofday for time
static inline void timer_stop(timer_info *t) {
  // Clock ticks
  t->m_end_clock_tick = __rdtsc();
  // Time
  struct timeval end;
  gettimeofday(&end, 0);
  t->m_end_time = ((double) end.tv_sec * 1000.0) + (double) end.tv_usec / 1000.0;

  // Accumulate values
  t->cnt++;
  t->acc_tick += t->m_end_clock_tick - t->m_start_clock_tick;
  t->acc_time += t->m_end_time - t->m_start_time;
}

// Description:
// Returns the number of clock ticks taken between start and stop
long long timer_get_last_ticks(timer_info *t) {
  return (t->m_end_clock_tick - t->m_start_clock_tick);
}

// Description:
// Returns the miliseconds taken between start and stop
double timer_get_last_time(timer_info *t) {
  return (t->m_end_time - t->m_start_time);
}

// Description:
// Returns the number of clock ticks taken between start and stop
long long timer_get_ticks(timer_info *t) {
  return t->acc_tick/(long long)t->cnt;
}

// Description:
// Returns the miliseconds taken between start and stop
double timer_get_time(timer_info *t) {
  return (t->acc_time);
}

