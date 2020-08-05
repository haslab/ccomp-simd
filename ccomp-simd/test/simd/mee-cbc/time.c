/******************************************************************************/
/******************************************************************************/
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <inttypes.h>

/* qsort() u64s numerically */
static int u64cmp (const void * left, const void * right)
{
   if (*(const uint64_t *)left > *(const uint64_t *)right) return 1;
   if (*(const uint64_t *)left < *(const uint64_t *)right) return -1;
   return 0;
}

/* Generate summary statistics from a list of u64s */
static void summarize(uint64_t *list, int n, uint64_t *count, uint64_t *avg, uint64_t *median, uint64_t *stddev, uint64_t *variance)
{
    qsort(list, n, sizeof(uint64_t), u64cmp);

    uint64_t p25 = list[ n / 4 ];
    uint64_t p50 = list[ n / 2 ];
    uint64_t p75 = list[ n - (n / 4)];
    uint64_t iqr = p75 - p25;

    /* Use the standard interquartile range rule for outlier detection */
    int64_t low = p25 - (iqr * 1.5);
    if (iqr > p25) {
        low = 0;
    }

    *avg = low;
        
    int64_t hi = p75 + (iqr * 1.5);
    /* Ignore overflow as we have plenty of room at the top */

    *count = 0;
    uint64_t sum = 0;
    uint64_t sum_squares = 0;
    uint64_t min = 0xFFFFFFFF;
    uint64_t max = 0;
    int i;

    for (i = 0; i < n; i++) {
        int64_t value = list[ i ];

        if (value < low || value > hi) {
            continue;
        }

        (*count)++;

        sum += value;
        sum_squares += value * value;

        if (value < min) {
            min = value; 
        }
        if (value > max) {
            max = value;
        }
    }

    *variance = sum_squares - (sum * sum);
    *median = p50;

    if (*count == 0) {
        *avg = 0;
    }
    else {
        *avg = sum / *count;
    }

    if (*count <= 1) {
        *stddev = 0;
    }
    else {
        *stddev = sqrt((*count * *variance) / (*count * (*count - 1)));
    }
}

inline static uint64_t rdtsc(){
    unsigned int bot, top;
    __asm__ __volatile__ ("rdtsc" : "=a" (bot), "=d" (top));
    return ((uint64_t) top << 32) | bot;
}

/******************************************************************************/
/******************************************************************************/

