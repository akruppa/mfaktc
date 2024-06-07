/*
This file is part of mfaktc.
Copyright (C) 2024 Alexander Kruppa

mfaktc is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

mfaktc is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
                                
You should have received a copy of the GNU General Public License
along with mfaktc.  If not, see <http://www.gnu.org/licenses/>.
*/

/* Add two unsigned longs to two unsigned longs with carry propagation from 
   low word (r1) to high word (r2). Any carry out from high word is lost. */

/* Undefine out for assertions */
#define NDEBUG 1
#include <assert.h>

static inline void
ularith_add_2ul_2ul (unsigned long *r1, unsigned long *r2, 
                         const unsigned long a1, const unsigned long a2)
{
#if defined(__x86_64__) && defined(__GNUC__)
  __asm__ (
    "addq %2, %0\n\t"
    "adcq %3, %1\n"
    : "+&r" (*r1), "+r" (*r2)
    : "rme" (a1), "rme" (a2)
    : "cc");
#elif defined(__i386__) && defined(__GNUC__)
  __asm__ (
    "addl %2, %0\n\t"
    "adcl %3, %1\n"
    : "+&r" (*r1), "+r" (*r2)
    : "g" (a1), "g" (a2)
    : "cc");
#else
  *r1 += a1;
  *r2 += a2 + (*r1 < a1);
#endif
}


/* Multiply two unsigned long "a" and "b" and put the result as 
   r2:r1 (r2 being the high word) */

static inline void
ularith_mul_ul_ul_2ul (unsigned long *r1, unsigned long *r2, 
                       const unsigned long a, const unsigned long b)
{  
#if defined(__x86_64__) && defined(__GNUC__)
  __asm__ (
    "mulq %3"
    : "=a" (*r1), "=d" (*r2)
    : "%0" (a), "rm" (b)
    : "cc");
#elif defined(__i386__) && defined(__GNUC__)
  __asm__ (
    "mull %3"
    : "=a" (*r1), "=d" (*r2)
    : "%0" (a), "rm" (b)
    : "cc");
#elif defined(__arm__) && defined(__GNUC__)
  __asm__ (
   "umull   %[r1], %[r2], %[a], %[b]\n\t"
  : [r1] "=&r" (*r1), [r2] "=&r" (*r2)
  : [a] "r" (a), [b] "r" (b)
  );
#elif LONG_BIT == 32
    uint64_t r = (uint64_t) a * b;
    *r1 = (unsigned long) r;
    *r2 = (unsigned long) (r >> 32);
#elif LONG_BIT == 64 && defined(HAVE_INT128)
    /* this code is useful for example on ARM processors (Raspberry Pi) */
    unsigned __int128 r = (unsigned __int128) a * b;
    *r1 = (unsigned long) r;
    *r2 = (unsigned long) (r >> 64);
#else
  const int half = LONG_BIT / 2;
  const unsigned long mask = (1UL << half) - 1UL;
  unsigned long t1, t2, p1, p2;

  t1 = (a & mask) * (b & mask);
  t2 = 0UL;
  p1 = (a >> half) * (b & mask);
  p2 = p1 >> half;
  p1 = (p1 & mask) << half;
  ularith_add_2ul_2ul (&t1, &t2, p1, p2);
  p1 = (a & mask) * (b >> half);
  p2 = p1 >> half;
  p1 = (p1 & mask) << half;
  ularith_add_2ul_2ul (&t1, &t2, p1, p2);
  t2 += (a >> half) * (b >> half);
  *r1 = t1; 
  *r2 = t2;
#endif
}

/* Integer division of a two ulong value a2:a1 by a ulong divisor. Returns
   quotient and remainder. */

static inline void
ularith_div_2ul_ul_ul (unsigned long *q, unsigned long *r, 
                           const unsigned long a1, const unsigned long a2, 
                           const unsigned long b)
{
  assert(a2 < b); /* Or there will be quotient overflow */
#if defined(__x86_64__) && defined(__GNUC__)
  __asm__ (
    "divq %4"
    : "=a" (*q), "=d" (*r)
    : "0" (a1), "1" (a2), "rm" (b)
    : "cc");
#elif defined(__i386__) && defined(__GNUC__)
  __asm__ (
    "divl %4"
    : "=a" (*q), "=d" (*r)
    : "0" (a1), "1" (a2), "rm" (b)
    : "cc");
#else
  mp_limb_t A[2] = {a1, a2};
  assert(sizeof(unsigned long) == sizeof(mp_limb_t));
  r[0] = mpn_divmod_1 (A, A, 2, b);
  q[0] = A[0];
#endif
}

/* Integer division of a two longint value by a longint divisor. Returns
   only remainder. */

static inline void
ularith_div_2ul_ul_ul_r (unsigned long *r, unsigned long a1,
                 const unsigned long a2, const unsigned long b)
{
  assert(a2 < b); /* Or there will be quotient overflow */
#if defined(__x86_64__) && defined(__GNUC__)
  __asm__ (
    "divq %3"
    : "+a" (a1), "=d" (*r)
    : "1" (a2), "rm" (b)
    : "cc");
#elif defined(__i386__) && defined(__GNUC__)
  __asm__ (
    "divl %3"
    : "+a" (a1), "=d" (*r)
    : "1" (a2), "rm" (b)
    : "cc");
#else
  mp_limb_t A[2] = {a1, a2};
  assert(sizeof(unsigned long) == sizeof(mp_limb_t));
  r[0] = mpn_divmod_1 (A, A, 2, b);
#endif
}

/* Compute (a*b) mod m. */

static inline unsigned long
mulmod_ul(const unsigned long a,
                  const unsigned long b, const unsigned long m)
{
  unsigned long t1, t2, r;
  ularith_mul_ul_ul_2ul(&t1, &t2, a, b);
  ularith_div_2ul_ul_ul_r (&r, t1, t2, m);
  return r;
}


static inline unsigned long
gcd_ul (unsigned long a, unsigned long b)
{
  unsigned long t;

  if (b == 0)
    return a;

  if (a >= b)
    a %= b;

  while (a > 0)
    {
      /* Here 0 < a < b */
      t = b % a;
      b = a;
      a = t;
    }

  return b;
}
