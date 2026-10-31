//===================================================================================================================================
// sumofsemiprimes2.c: Sums all primes and semiprimes <= x.
//===================================================================================================================================
// Author: Simon Goater Jan 2026
// Uses adaptaion of Legendre's prime counting method to calculate the sum of all primes and semiprimes less than or equal to 
// input x <= 10^19.
//
// COPYRIGHT NOTICE: Copying, modifying, and distributing with conspicuous attribution for any purpose is permitted.
// WARNING: 'Proof Of Concept' code only. Use entirely at own risk.
//===================================================================================================================================

#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <stdbool.h>
#include <assert.h>
#include <pthread.h>
#include "/home/simon/Mairsonsprimesieve.c" // https://github.com/FastAsChuff/Primes-List/blob/main/Mairsonsprimesieve.c
#ifndef alignof 
  #define alignof _Alignof
#endif
#define U128 unsigned __int128
#ifndef MIN
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#endif

// See https://math.stackexchange.com/questions/1378286/find-the-sum-of-all-primes-smaller-than-a-big-number/5118835#5118835

// gcc sumofsemiprimes2.c -o sumofsemiprimes2.bin -O3 -Wall -mssse3 -lm -lpthread

#define NUMOF32BITPRIMES 203280221
#define SOPISQRT10TO19 3162277660U // isqrt(10^19)
#define SOPPIISQRT10TO19 151876932 // pi(isqrt(10^19))
#define SOPPIISQRT10TO18 50847534 // pi(isqrt(10^18))
#define SOPPIISQRT10TO17 17082666 // pi(isqrt(10^17))
#define SOPPIISQRT10TO16 5761455 // pi(isqrt(10^16))

// RAM Requirements
// ================
// xi stack 151876932*sizeof(xivals_s) = up to 9.72GB
// Choose cache size...(diminishing returns)
//#define SOPXICACHESIZE1 // ~1GB
#define SOPXICACHESIZE2 // ~3.1GB
//#define SOPXICACHESIZE3 // ~16.6GB
//#define SOPXICACHESIZE4 // ~28.8GB
#ifdef SOPXICACHESIZE1 
#define SOPXICACHETYPE uint32_t
#define SOPXICACHEWIDTH 50000
#define SOPXICACHEHEIGHT 5133
#endif
#ifdef SOPXICACHESIZE2 
#define SOPXICACHETYPE uint32_t
#define SOPXICACHEWIDTH 90000
#define SOPXICACHEHEIGHT 8713
#endif
#ifdef SOPXICACHESIZE3 
#define SOPXICACHETYPE uint64_t
#define SOPXICACHEWIDTH 150000
#define SOPXICACHEHEIGHT 13848
#endif
#ifdef SOPXICACHESIZE4 
#define SOPXICACHETYPE uint64_t
#define SOPXICACHEWIDTH 200000
#define SOPXICACHEHEIGHT 17984
#endif

uint32_t isqrt(uint64_t n) {
  if (n < 2) return n;
  uint64_t ai = sqrt(n);
  while (!((ai <= n/ai) && ((ai+1) > n/(ai+1)))) {    
    ai = (ai + n/ai)/2;
  }
  return ai;
}

uint32_t icbrt(uint64_t n) {
  if (n < 2) return n;
  uint64_t ai = cbrt(n);
  while (!((ai <= n/(ai*ai)) && ((ai+1) > n/((ai+1)*(ai+1))))) {    
    ai = (2*ai + n/(ai*ai))/3;
  }
  return ai;
}

_Bool inascarrayu32(uint32_t n, uint32_t *array, uint64_t arraysize, uint64_t *index) {
  // Binary Search. Array is assumed sorted ascending. index largest st array[index] <= n.
  if (n < array[0]) {
    *index = -1;
    return false;
  }
  if (n >= array[arraysize-1]) {
    *index = arraysize-1;
    return true;
  }
  uint64_t leftix = 0;
  uint64_t rightix = arraysize-1;
  if (array[leftix] == n) {
    *index = leftix;
    return true;
  }
  if (array[rightix] == n) {  
    *index = rightix;
    return true;
  }
  uint64_t middleix = (leftix + rightix)/2;
  while (true) {
    if (array[middleix] == n) {
      *index = middleix;
      return true;
    }
    if (array[middleix] < n) {
      leftix = middleix;
    } else {
      rightix = middleix;
    }
    middleix = (leftix + rightix)/2;
    if (middleix == leftix) {
      *index = middleix;
      return array[middleix] == n;
    }
  } 
  assert(true == false); 
  return false;
}

void printU128(U128 n) {
  if (n == 0) {
    printf("0");
    return;
  }
  char buf[40] = {0};
  int bufix = 1;
  while (n) {
    buf[bufix++] = n % 10;
    n /= 10;
  }
  bufix--;
  while (bufix) printf("%c", '0' + buf[bufix--]);
}

typedef struct {
  U128 val1, val2; // xi(x, m) = va1 - p_m*val2 if both are not -1.
  uint64_t x; // x > 0 if element values can be used
  uint32_t m, isqrtx, piisqrtx; // m <= piisqrtx
} xivals_s;

U128 getxivals(uint64_t x, uint32_t m, uint32_t isqrtx, uint64_t piisqrtx, uint32_t *primes, uint64_t *primesums, uint32_t numprimes, SOPXICACHETYPE *xicachesmalls) {
  if (m == 0) return ((U128)(x+1)*x)/2;
  if (x == 0) return 0;
  if (m >= x) return 1;
  if (m <= numprimes) {
    if (primes[m-1] >= x) return 1;
  }
  if ((x < SOPXICACHEWIDTH) && (m < SOPXICACHEHEIGHT)) {
    if (xicachesmalls[x*SOPXICACHEHEIGHT + m] != (SOPXICACHETYPE)-1) return xicachesmalls[x*SOPXICACHEHEIGHT + m];
  }
  xivals_s *xivals = aligned_alloc(alignof(xivals_s), (m+7)*sizeof(xivals_s));
  assert(xivals); 
  for(uint64_t j=0; j<m+7; j++) xivals[j].x = 0;
  xivals[0].val1 = (U128)-1; 
  xivals[0].val2 = (U128)-1; 
  xivals[0].x = x; 
  xivals[0].m = m; 
  xivals[0].isqrtx = isqrtx; 
  xivals[0].piisqrtx = piisqrtx;
  uint64_t xivalsix = 0;
  while (true) {
    _Bool done = false; 
    if (xivals[xivalsix].m == 0) {
      xivals[xivalsix].val1 = ((U128)(xivals[xivalsix].x+1)*xivals[xivalsix].x)/2;
      xivals[xivalsix].val2 = 0;
    }    
    if ((xivals[xivalsix].x < SOPXICACHEWIDTH) && (xivals[xivalsix].m < SOPXICACHEHEIGHT)) {
      if (xicachesmalls[xivals[xivalsix].x*SOPXICACHEHEIGHT + xivals[xivalsix].m] != (SOPXICACHETYPE)-1) {
        xivals[xivalsix].val1 = xicachesmalls[xivals[xivalsix].x*SOPXICACHEHEIGHT + xivals[xivalsix].m];
        xivals[xivalsix].val2 = 0;
      }
    } 
    if (xivals[xivalsix].x <= primes[numprimes-1]) {
      if (xivals[xivalsix].m == xivals[xivalsix].piisqrtx) {
        uint64_t pix = 0;
        if (xivals[xivalsix].x >= 2) {
          inascarrayu32(xivals[xivalsix].x, primes, numprimes, &pix);
          pix++;
        }
        xivals[xivalsix].val1 = 1;
        if (pix) xivals[xivalsix].val1 += primesums[pix-1];
        if (xivals[xivalsix].piisqrtx) xivals[xivalsix].val1 -= primesums[xivals[xivalsix].piisqrtx-1];
        xivals[xivalsix].val2 = 0;
      }
    }   
    if (xivals[xivalsix].val1 == (U128)-1) {
      if (xivals[1+xivalsix].x) {
        //assert((xivals[xivalsix].x == xivals[1+xivalsix].x) && (xivals[xivalsix].m == 1+xivals[1+xivalsix].m));
        //assert((xivals[1+xivalsix].val1 != (U128)-1) && (xivals[1+xivalsix].val2 != (U128)-1));
        if (xivals[1+xivalsix].m) {
          xivals[xivalsix].val1 = xivals[1+xivalsix].val1 - primes[xivals[1+xivalsix].m-1]*xivals[1+xivalsix].val2;
        } else {
          xivals[xivalsix].val1 = xivals[1+xivalsix].val1;
        }
        xivals[1+xivalsix].x = 0;
      } else {
        xivals[1+xivalsix].x = xivals[xivalsix].x;
        xivals[1+xivalsix].m = xivals[xivalsix].m-1;
        xivals[1+xivalsix].isqrtx = xivals[xivalsix].isqrtx;
        xivals[1+xivalsix].piisqrtx = xivals[xivalsix].piisqrtx;
        xivalsix++;
        xivals[xivalsix].val1 = (U128)-1; 
        xivals[xivalsix].val2 = (U128)-1; 
        done = true;
      }
    }
    if (!done && (xivals[xivalsix].val2 == (U128)-1) && (xivals[xivalsix].val1 != (U128)-1)) {
      if (xivals[1+xivalsix].x) {
        //assert(xivals[xivalsix].x/primes[xivals[xivalsix].m-1] == xivals[1+xivalsix].x);
        //assert((xivals[1+xivalsix].val1 != (U128)-1) && (xivals[1+xivalsix].val2 != (U128)-1));
        if (xivals[1+xivalsix].m) {
          xivals[xivalsix].val2 = xivals[1+xivalsix].val1 - primes[xivals[1+xivalsix].m-1]*xivals[1+xivalsix].val2;
        } else {
          xivals[xivalsix].val2 = xivals[1+xivalsix].val1;
        }
    // s(x) = xi(x, pi(a)) + s(a) - 1 if a >= isqrt(x)
    // s(x) = xi(x, m) + s(p_m) - 1 if p_m >= isqrt(x)
    // s(x) = xi(x, m) + s(p_m) - 1 if m >= piisqrtx
    // s(x) = xi(x, m) + s(p_m) - 1 = xi(x, piisqrtx) + s(isqrtx) - 1 if m >= piisqrtx
    // xi(x, m) = xi(x, piisqrtx) + s(isqrtx) - s(p_m) if m >= piisqrtx
        if (1+xivals[1+xivalsix].m < xivals[xivalsix].m) {
          //assert(xivals[1+xivalsix].m == xivals[1+xivalsix].piisqrtx);
          if (xivals[1+xivalsix].piisqrtx) {
            xivals[xivalsix].val2 = (xivals[xivalsix].val2 + primesums[xivals[1+xivalsix].piisqrtx-1]) - primesums[xivals[xivalsix].m-2];
          } else {
            xivals[xivalsix].val2 -= primesums[xivals[xivalsix].m-2];
          }
        }
        xivals[1+xivalsix].x = 0;
      } else {
        xivals[1+xivalsix].x = xivals[xivalsix].x/primes[xivals[xivalsix].m-1];
        if (xivals[1+xivalsix].x) {
          xivals[1+xivalsix].isqrtx = isqrt(xivals[1+xivalsix].x);
          uint64_t piisqrtx2 = 0;
          if (xivals[1+xivalsix].isqrtx >= 2) {
            inascarrayu32(xivals[1+xivalsix].isqrtx, primes, numprimes, &piisqrtx2);
            piisqrtx2++;
          }
          xivals[1+xivalsix].piisqrtx = piisqrtx2;
          xivals[1+xivalsix].m = MIN(xivals[xivalsix].m-1, piisqrtx2);
          xivalsix++;
          xivals[xivalsix].val1 = (U128)-1; 
          xivals[xivalsix].val2 = (U128)-1; 
          done = true;
        } else {
          xivals[xivalsix].val2 = 0;
        }
      }
    }
    /*
    printf("%lu: x=%lu m=%u", xivalsix, xivals[xivalsix].x, xivals[xivalsix].m);
    if (xivals[xivalsix].val1 != (U128)-1) {
      printf(" val1=");
      printU128(xivals[xivalsix].val1);
    }
    if (xivals[xivalsix].val2 != (U128)-1) {
      printf(" val2=");
      printU128(xivals[xivalsix].val2);
    }
    if ((xivals[xivalsix].val1 != (U128)-1) && (xivals[xivalsix].val2 != (U128)-1)) {
      printf(" val=");
      U128 val = xivals[xivalsix].val1;
      if (xivals[xivalsix].m) val -= primes[xivals[xivalsix].m-1]*xivals[xivalsix].val2;
      printU128(val);
    }
    printf("\n");
    sleep(1);
    */
    if ((xivals[xivalsix].val2 != (U128)-1) && (xivals[xivalsix].val1 != (U128)-1)) {
      if (xivalsix == 0) break;
      xivalsix--;      
      //assert(((xivals[xivalsix].val1 != (U128)-1) && (xivals[xivalsix].val2 == (U128)-1)) || (xivals[xivalsix].val1 == (U128)-1));
    }
  }
  U128 xi = xivals[0].val1 - primes[m-1]*xivals[0].val2;
  free(xivals);
  return xi;
}

typedef struct {
  _Bool justxivals;
  uint16_t numthreads;
  uint16_t threadno;
  uint32_t m;
  uint32_t numprimes;
  uint32_t isqrtx;
  uint32_t piisqrtx;
  uint64_t x;
  uint32_t *primes;
  uint64_t *primesums;
  SOPXICACHETYPE *xicachesmalls;
  U128 result;
} getxiargs_s;

pthread_mutex_t threadblockmutex = PTHREAD_MUTEX_INITIALIZER;
uint64_t threadblocksize = 25; // number of prime divisors of x per thread.
uint64_t threadblockix = 0;

void *getxi(void *args) {
  getxiargs_s *getxiargs = args;
  _Bool justxivals = getxiargs->justxivals;
  uint16_t numthreads = getxiargs->numthreads;
  uint16_t threadno = getxiargs->threadno;
  uint32_t m = getxiargs->m;
  uint32_t numprimes = getxiargs->numprimes;
  uint32_t isqrtx = getxiargs->isqrtx;
  uint32_t piisqrtx = getxiargs->piisqrtx;
  uint64_t x = getxiargs->x;
  uint32_t *primes = getxiargs->primes;
  uint64_t *primesums = getxiargs->primesums;
  SOPXICACHETYPE *xicachesmalls = getxiargs->xicachesmalls;
  if (threadno && !justxivals) { // Calculates a partial result only of
    // sum_{i=0 to m-1} xi(x/p_{m-i}, m-1-i)p_{m-i} = x(x+1)/2 - xi(x,m)
    uint64_t ix = 0;
    uint64_t ixmax = 0;
    getxiargs->result = 0;
    while (true) {
      pthread_mutex_lock(&threadblockmutex);
      ix = threadblockix;
      threadblockix += threadblocksize;
      ixmax = threadblockix-1;
      pthread_mutex_unlock(&threadblockmutex);
      for (; (ix < m) && (ix <= ixmax); ix++) {
        getxiargs_s getxiargs3 = *getxiargs;
        getxiargs3.justxivals = true;
        getxiargs3.x = x/primes[m-ix-1];
        getxiargs3.isqrtx = isqrt(getxiargs3.x);
        uint64_t piisqrtnewx = 0;
        if (getxiargs3.isqrtx >= 2) {
          inascarrayu32(getxiargs3.isqrtx, primes, numprimes, &piisqrtnewx);
          piisqrtnewx++;
        }
        getxiargs3.piisqrtx = piisqrtnewx;
        getxiargs3.m = m-ix-1;
        getxi(&getxiargs3);
        getxiargs->result += primes[m-ix-1]*getxiargs3.result;
      }
      if (ix >= m) break;
    }
    return NULL;
  }
  if (m == 0) {
    getxiargs->result = ((U128)(x+1)*x)/2;
    return NULL;
  }
  if (x == 0) {
    getxiargs->result = 0;    
    return NULL;
  }
  if (m >= x) {
    getxiargs->result = 1;   
    return NULL;
  }
  if (m <= numprimes) {
    if (primes[m-1] >= x) {
      getxiargs->result = 1;   
      return NULL;
    }
  }
  if ((x < SOPXICACHEWIDTH) && (m < SOPXICACHEHEIGHT)) {
    if (xicachesmalls[x*SOPXICACHEHEIGHT + m] != (SOPXICACHETYPE)-1) {
      getxiargs->result = xicachesmalls[x*SOPXICACHEHEIGHT + m];   
      return NULL;
    }
  }
  if (piisqrtx) {
    if (m > piisqrtx) {    
      getxiargs_s getxiargs2 = *getxiargs;
      getxiargs2.m = piisqrtx;
      getxi(&getxiargs2);
      getxiargs->result = (getxiargs2.result + primesums[piisqrtx-1]) - primesums[m-1];   
      return NULL;
    }
  }
  uint32_t i=0;
  U128 val2s = 0;
  /*
  //===================================================================================================
  // The following loop significantly shortens the xivals array needed using
  // xi(x,m) = xi(x, m-i) - sum_{j=0 to i-1} p_{m-i+j+1}xi(x/p_{m-i+j+1}, m-i+j)
  // where xi(x,m) = s(x) + 1 - s(p_m) provided sqrt(x) <= p_m <= x.
  // This section can be commented out.
  //===================================================================================================
  if ((m > 1) && (m <= numprimes)) {
    while (((U128)((uint64_t)primes[m-i-2]*primes[m-i-2])*primes[m-i-1] >= x)) {
      if (x >= primes[m-i-1]) {
        U128 xoverpmi = x/primes[m-i-1];
        uint64_t pixoverpmi = 0;
        if (xoverpmi >= 2) {
          if (xoverpmi > primes[numprimes - 1]) break;
          inascarrayu32(xoverpmi, primes, numprimes, &pixoverpmi);
          pixoverpmi++;
        }
        val2s += primes[m-i-1]*(U128)primesums[pixoverpmi-1];
      }
      val2s -= primes[m-i-1]*((U128)primesums[m-i-2]-1);
      i++;
      if (m < 2+i) break;
    }
  }
  //===================================================================================================
  */
  if (justxivals) {
    getxiargs->result = getxivals(x, m-i, isqrtx, piisqrtx, primes, primesums, numprimes, xicachesmalls) - val2s;
    return NULL;
  }  
  getxiargs_s *getxithreadargs = aligned_alloc(alignof(getxiargs_s), numthreads*sizeof(getxiargs_s));
  for (uint32_t j=0; j<numthreads; j++) {
    getxithreadargs[j] = *getxiargs;
    getxithreadargs[j].justxivals = false;
    getxithreadargs[j].threadno = 1+j;
    getxithreadargs[j].m = m-i;
  }
  pthread_t *threads = malloc(numthreads*sizeof(pthread_t));
  for (uint32_t j=0; j<numthreads; j++) {
    pthread_create(&threads[j], NULL, getxi, &getxithreadargs[j]);
  }
  for (uint32_t j=0; j<numthreads; j++) pthread_join(threads[j], NULL);
  getxiargs->result = ((U128)x*(x+1))/2 - val2s;
  for (uint32_t j=0; j<numthreads; j++) getxiargs->result -= getxithreadargs[j].result;
  free(threads);
  free(getxithreadargs);
  return NULL;
}

uint64_t *makeprimesums(uint32_t *primes, uint32_t numprimes) {
  uint64_t sum = 0;
  uint64_t *primesums = malloc(numprimes*(sizeof(uint64_t)));
  if (primesums) {
    for (uint32_t i=0; i<numprimes; i++) primesums[i] = (sum += primes[i]);
  }
  return primesums;
}

U128 sumofprimes(uint16_t numthreads, uint64_t x, uint32_t **primes, uint64_t **primesums, uint32_t *numprimes, SOPXICACHETYPE *xicachesmalls, U128 *sumofsemiprimes) {
  if (x < 2) return 0;
  uint64_t pix;
  if (x <= (*primes)[*numprimes-1]) {
    inascarrayu32(x, *primes, *numprimes, &pix);
    if (sumofsemiprimes == NULL) return (*primesums)[pix];
  }
  uint32_t isqrtx = isqrt(x);
  if ((isqrtx > (*primes)[*numprimes - 1]) || ((isqrtx > 5000000U) && (*numprimes < NUMOF32BITPRIMES))) {
    free(*primes);
    free(*primesums);
    if (isqrtx > 5000000U) {
      *primes = Mairsonsprimesieve(0xffffffffu, numprimes);
    } else {
      *primes = Mairsonsprimesieve(2*isqrtx, numprimes);
    }
    assert(*primes);
    *primesums = makeprimesums(*primes, *numprimes);
    assert(*primesums);
  }
  uint64_t piisqrtx = 0;
  if (isqrtx >= 2) {
    inascarrayu32(isqrtx, *primes, *numprimes, &piisqrtx);
  }
  piisqrtx++;
  if (x <= (*primes)[*numprimes-1]) {
    *sumofsemiprimes = 0;
    for (uint32_t i=1; i<=piisqrtx; i++) {
      uint64_t xoverp = x/(*primes)[i-1];
      uint64_t pixoverp = 0;
      if (xoverp >= 2) {
        inascarrayu32(xoverp, *primes, *numprimes, &pixoverp);
        pixoverp++;
      }
      if (i >= 2) {
        *sumofsemiprimes += (U128)(*primes)[i-1]*((*primesums)[pixoverp-1] - (*primesums)[i-2]);
      } else {
        *sumofsemiprimes += (U128)(*primes)[i-1]*(*primesums)[pixoverp-1];
      }
    }
    return (*primesums)[pix];
  }
  uint32_t icbrtx = icbrt(x);
  uint64_t piicbrtx = 0;
  if (icbrtx >= 2) {
    inascarrayu32(icbrtx, *primes, *numprimes, &piicbrtx);
    piicbrtx++;
  }
  //printf("There are %lu primes <= %u.\n", piisqrtx, isqrtx);
  //exit(0);
  getxiargs_s getxiargs;
  getxiargs.justxivals = false;
  getxiargs.numthreads = numthreads;
  getxiargs.threadno = 0;
  getxiargs.m = piicbrtx;
  getxiargs.numprimes = *numprimes;
  getxiargs.isqrtx = isqrtx;
  getxiargs.piisqrtx = piisqrtx;
  getxiargs.x = x;
  getxiargs.primes = *primes;
  getxiargs.primesums = *primesums;
  getxiargs.xicachesmalls = xicachesmalls;
  getxiargs.result = 0;
  threadblockix = 0;
  getxi(&getxiargs);
  U128 res = getxiargs.result + sumofprimes(numthreads, icbrtx, primes, primesums, numprimes, xicachesmalls, NULL) - 1;
  if (sumofsemiprimes) *sumofsemiprimes = res;
  uint32_t i=piisqrtx;
  for (; ;) {
    res -= (*primes)[i-1]*(sumofprimes(numthreads, x/(*primes)[i-1], primes, primesums, numprimes, xicachesmalls, NULL) - (*primesums)[i-2]);
    if (i <= 1+piicbrtx) break;
    i--;
  }
  if (sumofsemiprimes) {
    *sumofsemiprimes -= res;
    for (i = piicbrtx; ;) {
      *sumofsemiprimes += (*primes)[i-1]*(sumofprimes(numthreads, x/(*primes)[i-1], primes, primesums, numprimes, xicachesmalls, NULL) - (*primesums)[i-2]);
      if (i == 2) break;
      i--;
    }
    *sumofsemiprimes += 2*sumofprimes(numthreads, x/2, primes, primesums, numprimes, xicachesmalls, NULL);
  }
  return res;
}

_Bool populatexicachesmalls(uint32_t *primes, uint64_t *primesums, uint32_t numprimes, SOPXICACHETYPE *xicachesmalls) {
  assert(numprimes >= SOPXICACHEHEIGHT);
  for (uint64_t x = 0; x<SOPXICACHEWIDTH; x++) {
    xicachesmalls[x*SOPXICACHEHEIGHT] = ((SOPXICACHETYPE)x*(x+1))/2;
  }  
  for (uint32_t m = 1; m<SOPXICACHEHEIGHT; m++) {
    for (uint64_t x = 0; x<SOPXICACHEWIDTH; x++) {
      xicachesmalls[x*SOPXICACHEHEIGHT + m] = xicachesmalls[x*SOPXICACHEHEIGHT + m-1] - primes[m-1]*xicachesmalls[(x/primes[m-1])*SOPXICACHEHEIGHT + m-1];
    }
  }
  return true;
}

int main(int argc, char* argv[]) {
  uint32_t numprimes;
  uint32_t *primes = Mairsonsprimesieve(100000000u, &numprimes);
  assert(primes);
  uint64_t *primesums = makeprimesums(primes, numprimes);
  assert(primesums);  
  /*
  uint32_t x = atol(argv[1]);
  assert(x >= 4);
  assert(x <= primes[numprimes-1]);
  uint32_t isqrtx = isqrt(x);
  uint64_t piisqrtx = 0;
  if (isqrtx >= 2) {
    inascarrayu32(isqrtx, primes, numprimes, &piisqrtx);
    piisqrtx++;
  }
  uint64_t rhoxim1 = 0; // rho(x, piisqrtx) = 0
  for (uint32_t i=piisqrtx; i >= 2;) {
    uint32_t xoverpi = x/primes[i-1];
    uint64_t pixoverpi = 0;
    if (xoverpi >= 2) {
      inascarrayu32(xoverpi, primes, numprimes, &pixoverpi);
      pixoverpi++;
    }    
    rhoxim1 += primes[i-1]*(primesums[pixoverpi-1] - primesums[i-2]);
    if (i == 2) break;
    i--;
  }
  uint32_t xoverpi = x/2;
  uint64_t pixoverpi = 0;
  if (xoverpi >= 2) {
    inascarrayu32(xoverpi, primes, numprimes, &pixoverpi);
    pixoverpi++;
  }    
  rhoxim1 += 2*primesums[pixoverpi-1];
  printf("rho(%u, 0) = %lu\n", x, rhoxim1);
  exit(0);
  */
  
  uint16_t numthreads = 8;
  if (argc > 1) numthreads = atoi(argv[1]);
  uint64_t xicachesmallsbytes = SOPXICACHEWIDTH*(SOPXICACHEHEIGHT*sizeof(SOPXICACHETYPE));
  SOPXICACHETYPE *xicachesmalls = aligned_alloc(alignof(SOPXICACHETYPE), xicachesmallsbytes);
  assert(xicachesmalls);  
  //memset(xicachesmalls, 0xffu, xicachesmallsbytes);
  printf("This program calculates the sum of all the prime and semiprime numbers less than or equal to input value x <= 10^19.\nAuthor: Simon Goater Jan 2026\nRAM requirement approx. %f GB.\nUsage: %s [numthreads]\n", 
(((double)sizeof(SOPXICACHETYPE)*SOPXICACHEWIDTH)*SOPXICACHEHEIGHT + (double)NUMOF32BITPRIMES*(sizeof(uint32_t) + sizeof(uint64_t)))/1000000000.0, argv[0]);
  printf("Populating cached values. Please wait...\n");
  assert(populatexicachesmalls(primes, primesums, numprimes, xicachesmalls));
  while (true) {
    uint64_t x;
    printf("Enter x: ");
    fflush(stdout);
    assert(1 == scanf("%lu", &x));
    assert(x <= 10000000000000000000ULL);
    printf("Calculating sum of semiprimes less than or equal to %lu.\n", x);  
    uint64_t timestart = time(0);
    U128 sumofsemiprimes = 0;
    U128 result = 0;
    if (x >= 4) {
      result = sumofprimes(numthreads, x, &primes, &primesums, &numprimes, xicachesmalls, &sumofsemiprimes);
    } else {
      if (x == 2) result = 2;
      if (x == 3) result = 5;
    }
    uint64_t timeend = time(0);
    printf("The sum of primes less than or equal to %lu is ", x); 
    printU128(result);
    printf(".\n");
    printf("The sum of semiprimes less than or equal to %lu is ", x); 
    printU128(sumofsemiprimes);
    printf(".\n");
    //U128 sumofprimesquares = 0; // Use this if you want to calculate the sum of squarefree semiprimes.
    //for (uint32_t i=0; i<numprimes; i++) {
    //  uint32_t p = primes[i];
    //  uint64_t psqrd = (uint64_t)p*p;
    //  if (psqrd > x) break;
    //  sumofprimesquares += psqrd;
    //}
    //printf("The sum of prime squares less than or equal to %lu is ", x); 
    //printU128(sumofprimesquares);
    //printf(".\n");
    uint64_t timesecs = timeend - timestart;
    if (timesecs > 5) printf("%f Gx/s\n", x/(1000000000.0*timesecs));
    uint64_t timehrs = timesecs / 3600;
    uint64_t timemins = (timesecs - (3600*timehrs)) / 60;
    timesecs -= 60*(timemins + 60*timehrs);
    printf("Time: ");
    if (timehrs) printf("%lu hrs ", timehrs);
    if (timehrs || timemins) printf("%lu mins ", timemins);
    printf("%lu secs\n", timesecs);
  }  
}
// The sum of semiprimes less than or equal to 219876543210 is 3254370637080591193752.
// The sum of semiprimes less than or equal to 3219876543210 is 651013321707241253384605.
// The sum of semiprimes less than or equal to 43219876543210 is 110227308983448433469906676.
// The sum of all 11715902308080 semiprimes less than or equal to 100000000000000 is 578922111059938926290324483.
// The sum of all 111329817298881 semiprimes less than or equal to 1000000000000000 is 55051942194475245464480994431.
// The sum of all 1061057292827269 semiprimes less than or equal to 10000000000000000 is 5250250649878123471953045013441.
// The sum of all 10139482913717352 semiprimes less than or equal to 100000000000000000 is 502002949938209191945012706651297.
// Sum of semiprimes < 10^n = 0, 19, 1707, 146158, 12736914, 1138479765, 102604509687, 9322298311255, 854762170949394, 79000703096467991, 7350470907269726150, 687820221030088972220, 64678249335640715257806, 6107791297866477228634016, 578922111059938926290324483, 55051942194475245464480994431, 5250250649878123471953045013441, 502002949938209191945012706651297
