/*
This file is part of mfaktc.
Copyright (C) 2009, 2010, 2011, 2013, 2014  Oliver Weihe (o.weihe@t-online.de)

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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"
#include "compatibility.h"

#define SIEVE_PRIMES_EXTRA 25

static const int sieve_debugging_output = 0;
static const int TRACE_FUNCTION_CALLS = 32;
static const int TRACE_HEXDUMP_SIEVE = 64;
static const int TRACE_SKIPPED_PRIMES = 128;
static const int TRACE_K = 256;

/* yeah, I like global variables :) */
/* With MORE_CLASSES, sieve_base stores pattern of sieving 13, 17, 19 and 23. SIEVE_SIZE must therefore be a multiple of 96577 */
/* Without MORE_CLASSES, sieve_base stores pattern of sieving 11, 13, 17 and 19. SIEVE_SIZE must therefore be a multiple of 46189  */
static unsigned int *sieve, *sieve_base, mask0[32] ,mask1[32];
static int prime_base[SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA], primes[SIEVE_PRIMES_MAX], k_init[SIEVE_PRIMES_MAX], last_sieve;

/** Modular multiplication
 *  returns a*b % m
 */
static inline unsigned int mulmod(const unsigned int a, const unsigned int b, const unsigned int m) {
    unsigned long long product = (unsigned long long) a * (unsigned long long) b;
    return (unsigned int) (product % m);
}

int
class_needed(unsigned int exp, unsigned long long int k_min, unsigned int c,
             unsigned int num_classes, int verbosity)
{
/*
checks whether the class c must be processed or can be ignored at all because
all factor candidates within the class c are a multiple of 3, 5, 7 or 11 (11
only if MORE_CLASSES is definied) or are 3 or 5 mod 8 (Mersenne) or are 5 or 7 mod 8 (Wagstaff)

k_min *MUST* be aligned in that way that k_min is in class 0!
*/
  assert(k_min % num_classes == 0);
  assert(exponent % 2 == 1);
  const unsigned long long int kc = k_min + c;
  const unsigned int d_mod_8 = (2 * (exp %  8) * (kc %  8) + 1) %  8;
  if (0)
    printf("class_needed(exp = %u, k_min = %llu, c = %u, num_classes = %u, verbosity = %d), kc=%llu\n",
           exp, k_min, c, num_classes, verbosity, kc);
#ifdef WAGSTAFF
  /* Prime divisors of Wagstaff numbers 2^n+1 are 1 or 3 (mod 8).
We want 2^n==-1 (mod p).
If p is 1 (mod 8), then 2 is a QR, -1 is a QR, satisfied for any exponent.
If p is 3 (mod 8), then 2 is a QNR, -1 is a QNR, satisfied for odd exponents.
If p is 5 (mod 8), then 2 is a QNR, -1 is a QR, satisfied for even exponents.
If p is 7 (mod 8), then 2 is a QR, -1 is a QNR, never satisfied.
 */
  if (d_mod_8 != 1 && d_mod_8 != 3) {
      if (verbosity >= 2)
        printf("Don't need class %u (mod %u) because it is %u (mod 8) which "
               "contains no divisors of Wagstaff numbers\n", c, num_classes, d_mod_8);
      return 0;
  }
#else /* Mersennes */
  /* Divisors of Mersenne numbers are 1 or 7 (mod 8) */
  if (d_mod_8 != 1 && d_mod_8 != 7) {
      if (verbosity >= 2)
        printf("Don't need class %u (mod %u) because it is %u (mod 8) which "
               "contains no divisors of Mersenne numbers\n", c, num_classes, d_mod_8);
      return 0;
  }
#endif
  unsigned long g = gcd_ul(2 * (exp % num_classes) * (kc % num_classes) + 1, num_classes);
  if (g != 1) {
      if (verbosity >= 2)
        printf("Don't need class %u (mod %u) because all entries are divisible by %lu\n",
               c, num_classes, g);
      return 0;
  }

  return 1;
}

/** Modular exponentiation
 * returns base^exponent % m
 */
static unsigned int powmod(const unsigned int base, const unsigned int exponent, const unsigned int m) {
    unsigned int t = exponent, basepow = base;
    unsigned int result = 1;
    if (exponent == 0) return 1;
    while (t > 1) {
      if (t % 2 == 1) {
        result = mulmod(result, basepow, m);
      }
      basepow = mulmod(basepow, basepow, m);
      t = t / 2;
    }
    result = mulmod(result, basepow, m); /* Handle MSB */

    return result;
}

void hexdump(const void *p, const size_t len) {
  const unsigned int *p_ul = (const unsigned int *)p;
  for (size_t i = 0; i < len; i++) {
    printf("%08x", p_ul[i]);
  }
  printf("\n");
}

/* the sieve_table contains the number of bits set in n (sieve_table[n][8]) and
the position of the set bits
(sieve_table[n][0]...sieve_table[n][<number of bits set in n>-1])
for 0 <= n < 256 */
static unsigned int sieve_table[256][9];

static inline unsigned int idx_to_mask(unsigned int idx) {
    if (0) {
        return 1U << idx;
    } else {
        return mask1[idx];
    }
}

static inline unsigned int sieve_get_bit(unsigned int *array,unsigned int bit)
{
  unsigned int chunk;
  chunk=bit>>5;
  bit&=0x1F;
  return array[chunk] & idx_to_mask(bit);
}

static inline void sieve_set_bit(unsigned int *array,unsigned int bit)
{
  unsigned int chunk;
  chunk=bit>>5;
  bit&=0x1F;
  array[chunk] |= idx_to_mask(bit);
}

static inline void sieve_clear_bit(unsigned int *array,unsigned int bit)
{
  unsigned int chunk;
  chunk=bit>>5;
  bit&=0x1F;
  array[chunk] &= ~idx_to_mask(bit);
}
//#define sieve_clear_bit(ARRAY,BIT) asm("btrl  %0, %1" : /* no output */ : "r" (BIT), "m" (*ARRAY) : "memory", "cc" )
//#define sieve_clear_bit(ARRAY,BIT) ARRAY[BIT>>5]&=mask0[BIT&0x1F]

unsigned int* sieve_malloc(unsigned int size)
{
  unsigned int *array;
  if(size==0)return NULL;
  array=(unsigned int*)malloc((((size-1)>>5)+1)*4);
  return array;
}

void sieve_init()
{
  int i,j,k;
  for(i=0;i<32;i++)
  {
    mask1[i]=1<<i;
    mask0[i]=0xFFFFFFFF-mask1[i];
  }
  sieve=sieve_malloc(SIEVE_SIZE);
  sieve_base=sieve_malloc(SIEVE_SIZE);

  /* This generates a table of primes by checking for each odd integer j whether
     it is divisible by any of the already-known primes <= sqrt(j) */
  prime_base[0]=3;
  i=0;j=3;
  while(i < (SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA))
  {
    k=0;
    while(prime_base[k]*prime_base[k]<=j)
    {
      if(j%prime_base[k]==0)
      {
        j+=2;
        k=0;
      }
      else
      {
        k++;
      }
    }
    prime_base[i]=j;
    i++;
    j+=2;
  }
  for(i=0;i<256;i++)
  {
    sieve_table[i][8]=0;
    for(j=0;j<8;j++)
    {
      if(i&(1<<j))
      {
        sieve_table[i][sieve_table[i][8]++]=j;
      }
    }
  }
}

void sieve_free()
{
  free(sieve);
  free(sieve_base);
}

int sieve_euclid_modified(int j, int n, int r)
/*
(k*j) % n = r
calculates and returns k 
*/
{
/* using long long int because I'm too lazy to figure out where I can live with
smaller ints */
  long long int nn,nn_old,jj,pi0,pi1,pi2,qi0,qi1,qi2,tmp;
  
  nn_old=n;
  jj=j;
  
  if(r==0)return 0;	/* trivially! */
  if(j==1)return r;	/* easy, isn't it? */

/*** step 0 ***/
  qi0=nn_old/jj;
  nn=nn_old%jj;
  pi0=0;
  nn_old=jj;
  jj=nn;

  if(jj==1)		/* qi0 * j = -1 mod n     FIXME, is the describtion correct?*/
  {
    tmp=((-r*qi0) % n) + n;
    return (int)tmp;
  }

/*** step 1 ***/
  qi1=qi0;
  qi0=nn_old/jj;
  nn=nn_old%jj;
  pi1=pi0;
  pi0=r;
  nn_old=jj;
  jj=nn;

/*** step 2+ ***/
  while(nn)
  {
    qi2=qi1;
    qi1=qi0;
    qi0=nn_old/jj;
    nn=nn_old%jj;
    pi2=pi1;
    pi1=pi0;
    pi0=(pi2-pi1*qi2)%n;
    if(pi0<0)pi0+=n;
    nn_old=jj;
    jj=nn;
  }

  tmp=(pi1-pi0*qi1)%n;
  if(tmp<0)tmp+=n;

  return (int)tmp;
}

void sieve_init_class(unsigned int exp, unsigned long long int k_start, int sieve_limit)
{
  int i,j,k,p;
  int ii,jj;

  if (sieve_debugging_output & TRACE_FUNCTION_CALLS) {
    printf("sieve_init_class(exp=%u, k_start=%llu, sieve_limit=%d)\n",
           exp, k_start, sieve_limit);
  }

/* copy <sieve_limit> primes from prime_base[] to primes[] excluding any
primes which divide the exponent itself. Because factors are
2 * k * <exp> + 1 it is not a good idea to use divisors of <exp> for sieving.
Additionally primes which are factors of M<exp> are removed. It
would be sufficient add an initial offset for those primes but removing them
allows to find composite factors. */
  i = 0; j = 0;
  while(i < sieve_limit)
  {
    if(j >= (SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA))
    {
      printf("ERROR: SIEVE_PRIMES_EXTRA is too small, contact the author!\n");
      exit(EXIT_FAILURE);
    }
    /* Don't sieve by primes that divide the exponent. Since candidate
     * factors are of the form f = k*exp+1, a prime p | exp would always
     * have f % p = 1 and thus cannot divide any candidate divisor, i.e.,
     * it never hits in the sieve at all. Leaving them in would lead to an
     * unsolvable modular inverse when the sieve initialisation code tries
     * to calculate the first location that gets hit. */
    const int divides_exponent = exp % prime_base[j] == 0;

    /* If this prime is a factor of 2^exp-1, then we don't use it for
     * sieving so that any factors divisible by this prime are correctly
     * reported. */
    const int is_factor = powmod(2, exp, prime_base[j]) == 1;

    if(!divides_exponent && !is_factor)
    {
      primes[i++] = prime_base[j];
    }
    j++;
  }

  for(i=0;i<sieve_limit;i++)
  {
    p=primes[i];
    if (NUM_CLASSES % p == 0) {
      if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
        printf("%s():%d skipping primes[%d] = %d because it divides "
               "NUM_CLASSES = %d\n", __func__, __LINE__, i, p, NUM_CLASSES);
      }
      continue;
    }
    k=0;
// oldest version, explains what happens here a little bit */    
//    while((2 * (exp%p) * ((k_start+k*NUM_CLASSES)%p)) %p != (p-1))k++;


/* second version, expensive mod is avoided as much as possible, but it is
still a brute force trail&error method */
/*    ii=(2 * (exp%p) * (k_start%p))%p;
    jj=(2 * (exp%p) * (NUM_CLASSES%p))%p;
    while(ii != (p-1))
    {
      ii+=jj;
      if(ii>=p)ii-=p;
      k++;
    }
    k_init[i]=k;*/

/* third version using a modified euclidean algorithm */
    ii=(2ULL * (exp%p) * (k_start%p))%p;
    jj=(2ULL * (exp%p) * (NUM_CLASSES%p))%p;

    k = sieve_euclid_modified(jj, p, p-(1+ii));
    k_init[i]=k;

// error checking
    unsigned long long int check;
    check = k_start + (unsigned long long int) k * NUM_CLASSES;
    check %= p;
    check *= exp;
    check <<= 1;
    check %= p;
    /* We want (k_start + k * NUM_CLASSES) * exp * 2 + 1 == 0 (mod p) */
    /* i.e.,   k == (-1/2/exp - k_start) / NUM_CLASSES (mod p) */
    if(k < 0 || k >= p || check != (p-1))
    {
      printf("calculation of k_init[%d] failed!\n",i);
      printf("  k_start= %" PRIu64 "\n",k_start);
      printf("  exp= %u\n",exp);
      printf("  ii= %d\n",ii);
      printf("  jj= %d\n",jj);
      printf("  k= %d\n",k);
      printf("  p= %d\n",p);
      printf("  check= %" PRId64 "\n",check);
    }
  }
  
  for(i=0;i<SIEVE_SIZE;i++)sieve_set_bit(sieve_base,i);
  if (sieve_debugging_output & TRACE_HEXDUMP_SIEVE) {
    printf("%s():%d sieve_base[] = ",  __func__, __LINE__);
    hexdump(sieve_base, 10);
  }

  unsigned long remaining_sieve_size_divisors = SIEVE_SIZE_DIVISORS;
/* presieve the primes that divide SIEVE_SIZE_DIVISORS in sieve_base */
  for(i=0;i<sieve_limit && remaining_sieve_size_divisors > 1;i++)
  {
    p=primes[i];
    if (remaining_sieve_size_divisors % p != 0) {
      if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
        printf("%s():%d skipping primes[%d] = %d because it does not divide "
               "SIEVE_SIZE_DIVISORS = %d\n",
               __func__, __LINE__, i, p, SIEVE_SIZE_DIVISORS);
      }
      continue;
    }
    remaining_sieve_size_divisors /= p;
    /* Primes that divide NUM_CLASSES are never sieved here, even if
       NUM_CLASSES and SIEVE_SIZE_DIVISORS are not coprime */
    if (NUM_CLASSES % p == 0) {
      if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
        printf("%s():%d skipping primes[%d] = %d because it divides "
               "NUM_CLASSES = %d\n", __func__, __LINE__, i, p, NUM_CLASSES);
      }
      continue;
    }
    j=k_init[i];
    if (sieve_debugging_output & TRACE_K) {
      printf("%s():%d sieving primes[%d] = <%d, %d>\n", __func__, __LINE__, i, p, j);
    }
    while(j<SIEVE_SIZE)
    {
//if((2 * (exp%p) * ((k_start+j*NUM_CLASSES)%p)) %p != (p-1))printf("EEEK: sieve: p=%d j=%d k=%" PRIu64 "\n",p,j,k_start+j*NUM_CLASSES);
      sieve_clear_bit(sieve_base,j);
      j+=p;
    }
//    k_init[i]=j-SIEVE_SIZE;
  }
  if (remaining_sieve_size_divisors != 1) {
    printf("SIEVE_SIZE_DIVISORS=%lu invalid, contains unsieved primes or is not "
           "squarefree.\nAfter dividing out sieved primes, %lu remains\n",
           (unsigned long) SIEVE_SIZE_DIVISORS, remaining_sieve_size_divisors);
    exit(EXIT_FAILURE);
  }
  if (sieve_debugging_output & TRACE_HEXDUMP_SIEVE) {
    printf("%s():%d sieve_base[] = ",  __func__, __LINE__);
    hexdump(sieve_base, 10);
  }
  last_sieve = SIEVE_SIZE;
}


void sieve_candidates(int ktab_size, unsigned int *ktab, int sieve_limit)
{
  int i=-1,ii,j,k=0,p,c=0,ic;
  unsigned int s,sieve_table_8,*sieve_table_;
  unsigned int mask; //, index, index_max;
  unsigned int *ptr, *ptr_max;

  if (sieve_debugging_output & TRACE_FUNCTION_CALLS) {
    printf("sieve_candidates(ktab_size=%d, ktab=%p, sieve_limit=%d)\n",
           ktab_size, ktab, sieve_limit);
  }

#ifdef RAW_GPU_BENCH
//  quick hack to "speed up the siever", used for GPU-code benchmarks  
  for(i=0;i<ktab_size;i++)ktab[i]=i;
  return;
#endif  

  if(last_sieve < SIEVE_SIZE)
  {
    i=last_sieve;
    c=-i;
    goto _ugly_goto_in_siever;
  }

  while(k<ktab_size)
  {
//printf("sieve_candidates(): main loop start\n");
    memcpy(sieve, sieve_base, ((SIEVE_SIZE-1)>>3)+1);

/*
The first few primes in the sieve have their own code. Since they are small
they have many iterations in the inner loop. At the cost of some
initialisation we can avoid calls to sieve_clear_bit() which calculates
chunk and bit position in chunk on each call.
Every 32 iterations they hit the same bit position so we can make use of
this behaviour and precompute them. :)
*/
    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(i=0;i<SIEVE_SPLIT;i++)
    {
      p=primes[i];
      if (NUM_CLASSES % p == 0) {
        if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
          printf("%s():%d skipping primes[%d] = %d because it divides "
                 "NUM_CLASSES = %d\n", __func__, __LINE__, i, p, NUM_CLASSES);
        }
        continue;
      }
      if (SIEVE_SIZE_DIVISORS % p == 0) {
        if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
          printf("%s():%d skipping primes[%d] = %d because it divides "
                 "SIEVE_SIZE_DIVISORS = %d\n",
                 __func__, __LINE__, i, p, SIEVE_SIZE_DIVISORS);
        }
        continue;
      }
      j=k_init[i];
//printf("sieve: %d\n",p);
      for(ii=0; ii<32; ii++)
      {
        mask = mask0[j & 0x1F];
/*
        index = j >> 5;
        index_max = SIEVE_SIZE >> 5;
        if(index_max + (j & 0x1F) < SIEVE_SIZE)index_max++;
        while(index < index_max)
        {
          sieve[index] &= mask;
          index += p;
        }
        j+=p;
      }
      j = (index<<5) + ((j-p) & 0x1F);
      while(j>=SIEVE_SIZE)j-=p;
      j+=p;
      k_init[i]=j-SIEVE_SIZE;*/

        ptr = &(sieve[j>>5]);
        ptr_max = &(sieve[SIEVE_SIZE >> 5]);
        if( (j & 0x1F) < (SIEVE_SIZE & 0x1F))ptr_max++;
        while(ptr < ptr_max) /* inner loop, lets kick out some bits! */
        {
          *ptr &= mask;
          ptr += p;
        }
        j+=p;
      }
      j = ((int)(ptr - sieve)<<5) + ((j-p) & 0x1F); /* D'oh! Pointer arithmetic... but it is faster! */
      j -= SIEVE_SIZE;
      k_init[i] = j % p;
    }

    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(i=SIEVE_SPLIT;i<sieve_limit;i++)
    {
      p=primes[i];
      if (NUM_CLASSES % p == 0) {
        if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
          printf("%s():%d skipping primes[%d] = %d because it divides "
                 "NUM_CLASSES = %d\n", __func__, __LINE__, i, p, NUM_CLASSES);
        }
        continue;
      }
      if (SIEVE_SIZE_DIVISORS % p == 0) {
        if (sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
          printf("%s():%d skipping primes[%d] = %d because it divides "
                 "SIEVE_SIZE_DIVISORS = %d\n",
                 __func__, __LINE__, i, p, SIEVE_SIZE_DIVISORS);
        }
        continue;
      }
      j=k_init[i];
//printf("sieve: %d\n",p);
      while(j<SIEVE_SIZE)
      {
        sieve_clear_bit(sieve,j);
        j+=p;
      }
      k_init[i]=j-SIEVE_SIZE;
    }
    
/*
we have finished sieving and now we need to translate the remaining bits in
the sieve to the correspondic k_tab offsets
*/    

/* part one of the loop:
Get the bits out of the sieve until i is a multiple of 32
this is going to fail if ktab has less than 32 elements! */
    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(i=0;(i<SIEVE_SIZE) && (i&0x1F);i++)
    {
_ugly_goto_in_siever:
      if(sieve_get_bit(sieve,i))
      {
        ktab[k++]=i+c;
        if(k >= ktab_size)
        {
          last_sieve=i+1;
          return;
        }
      }
    }
/* part two of the loop:
Get the bits out of the sieve until
a) we're close the end of the sieve
or
b) ktab is nearly filled up */
    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(;i<(SIEVE_SIZE&0xFFFFFFE0) && k<(ktab_size-33);i+=32)	// thirty-three!!!
    {
      ic=i+c;
      s=sieve[i>>5];
//#define SIEVER_OLD_METHOD
#ifdef SIEVER_OLD_METHOD
      sieve_table_=sieve_table[ s     &0xFF];
      for(p=0;p<sieve_table_[8];p++) ktab[k++]=ic   +sieve_table_[p];
      
      sieve_table_=sieve_table[(s>>8 )&0xFF];
      for(p=0;p<sieve_table_[8];p++) ktab[k++]=ic +8+sieve_table_[p];
      
      sieve_table_=sieve_table[(s>>16)&0xFF];
      for(p=0;p<sieve_table_[8];p++) ktab[k++]=ic+16+sieve_table_[p];
      
      sieve_table_=sieve_table[ s>>24      ];
      for(p=0;p<sieve_table_[8];p++) ktab[k++]=ic+24+sieve_table_[p];

#else // not SIEVER_OLD_METHOD
      sieve_table_=sieve_table[ s     &0xFF];
      sieve_table_8=sieve_table_[8];
      ktab[k  ]=ic+sieve_table_[0];
      ktab[k+1]=ic+sieve_table_[1];
      ktab[k+2]=ic+sieve_table_[2];
      ktab[k+3]=ic+sieve_table_[3];
      if(sieve_table_8>4)
      {
        ktab[k+4]=ic+sieve_table_[4];
        ktab[k+5]=ic+sieve_table_[5];
        ktab[k+6]=ic+sieve_table_[6];
        ktab[k+7]=ic+sieve_table_[7];
      }
      k+=sieve_table_8;
      
      sieve_table_=sieve_table[(s>>8 )&0xFF];
      sieve_table_8=sieve_table_[8];
      ic+=8;
      ktab[k  ]=ic+sieve_table_[0];
      ktab[k+1]=ic+sieve_table_[1];
      ktab[k+2]=ic+sieve_table_[2];
      ktab[k+3]=ic+sieve_table_[3];
      if(sieve_table_8>4)
      {
        ktab[k+4]=ic+sieve_table_[4];
        ktab[k+5]=ic+sieve_table_[5];
        ktab[k+6]=ic+sieve_table_[6];
        ktab[k+7]=ic+sieve_table_[7];
      }
      k+=sieve_table_8;
      
      sieve_table_=sieve_table[(s>>16)&0xFF];
      sieve_table_8=sieve_table_[8];
      ic+=8;
      ktab[k  ]=ic+sieve_table_[0];
      ktab[k+1]=ic+sieve_table_[1];
      ktab[k+2]=ic+sieve_table_[2];
      ktab[k+3]=ic+sieve_table_[3];
      if(sieve_table_8>4)
      {
        ktab[k+4]=ic+sieve_table_[4];
        ktab[k+5]=ic+sieve_table_[5];
        ktab[k+6]=ic+sieve_table_[6];
        ktab[k+7]=ic+sieve_table_[7];
      }
      k+=sieve_table_8;
      
      sieve_table_=sieve_table[ s>>24      ];
      sieve_table_8=sieve_table_[8];
      ic+=8;
      ktab[k  ]=ic+sieve_table_[0];
      ktab[k+1]=ic+sieve_table_[1];
      ktab[k+2]=ic+sieve_table_[2];
      ktab[k+3]=ic+sieve_table_[3];
      if(sieve_table_8>4)
      {
        ktab[k+4]=ic+sieve_table_[4];
        ktab[k+5]=ic+sieve_table_[5];
        ktab[k+6]=ic+sieve_table_[6];
        ktab[k+7]=ic+sieve_table_[7];
      }
      k+=sieve_table_8;
#endif      
    }
/* part three of the loop:
Get the bits out of the sieve until
a) sieve ends
or
b) ktab is full */    
    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(;i<SIEVE_SIZE;i++)
    {
      if(sieve_get_bit(sieve,i))
      {
        ktab[k++]=i+c;
        if(k >= ktab_size)
        {
          last_sieve=i+1;
          return;
        }
      }
    }
    c+=SIEVE_SIZE;
  }
  last_sieve=i;
}
