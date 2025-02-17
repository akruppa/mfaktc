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
#include <errno.h>
#include <assert.h>

#include "params.h"
#include "compatibility.h"
#include "ularith.h"

#define SIEVE_PRIMES_EXTRA 25

static const int TRACE_FUNCTION_CALLS = 32;
static const int TRACE_HEXDUMP_SIEVE = 64;
static const int TRACE_SKIPPED_PRIMES = 128;
static const int TRACE_K = 256;
static const int sieve_debugging_output = 0;

/* yeah, I like global variables :) */
static unsigned int *sieve;

/**
 * @brief A pattern of sieving the primes in SIEVE_SIZE_DIVISORS
 * With MORE_CLASSES, it stores the pattern of sieving 13, 17, 19 and 23.
 * sieve_size must therefore be a multiple of 96577. Without MORE_CLASSES,
 * it stores the pattern of sieving 11, 13, 17 and 19. sieve_size must
 * therefore be a multiple of 46189.
 */
static unsigned int *sieve_base;

/**
 * @brief Mask with one 0 bit
 * The mask0[i] word contains a 0 bit in the i-th position and 1 bits
 * everywhere else.
 */
static unsigned int mask0[32];

/**
 * @brief Mask with one 1 bit
 * The mask1[i] word contains a 1 bit in the i-th position and 0 bits
 * everywhere else.
 */
static unsigned int mask1[32];

/**
 * @brief List of odd primes
 * Contains {3, 5, 7, 11, 13, 17, ...} 
 */
static int prime_base[SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA];

/**
 * @brief List of odd primes without "bad" primes
 * A copy of prime_base, but with primes removed that should not be used for
 * sieving. Removed primes are those that divide the exponent e and those that
 * divide 2^e-1.
 */
static int primes[SIEVE_PRIMES_MAX];
static int k_init[SIEVE_PRIMES_MAX], last_sieve;
static int sieve_size_divisors_primes[32];
static size_t sieve_size_divisors_nr_primes;

/** Modular multiplication
 *  returns a*b % m
 */
static inline unsigned int mulmod(const unsigned int a, const unsigned int b, const unsigned int m) {
    unsigned long long product = (unsigned long long) a * (unsigned long long) b;
    return (unsigned int) (product % m);
}

int compute_sieve_size(int limit, int divisors)
{
  return ((limit<<13) - (limit<<13) % divisors);
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
  assert(exp % 2 == 1);
  const unsigned long long int kc = k_min + c;
  const unsigned int d_mod_8 = (2 * (exp %  8) * (kc %  8) + 1) %  8;
  if (sieve_debugging_output & TRACE_FUNCTION_CALLS)
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

static size_t
sieve_size_in_words(unsigned int size) {
  if (size == 0)
    return 0;
  return ((size-1)>>5)+1;
}

unsigned int* sieve_malloc(unsigned int size, const char *name)
{
  unsigned int *array;
  if(size==0)return NULL;
  array=(unsigned int*)malloc(sieve_size_in_words(size)*sizeof(unsigned int));
  if (array == NULL) {
    fprintf(stderr, "Could not allocate memory for %s: %s\n",
            name, strerror(errno));
    exit(EXIT_FAILURE);
  }
  return array;
}

/* This generates a table of primes by checking for each odd integer j whether
   it is divisible by any of the already-known primes <= sqrt(j) */
static void
fill_with_odd_primes(int *primes, const int nr_primes)
{
  int i; /* The index of the next entry in primes to be filled */
  int j; /* The value of the next candidate prime */
  int k; /* primes[k] is used for trial dividing the j values */

  if (nr_primes <= 0)
    return;
  
  primes[0]=3;
  i=0; j=3;
  while(i < nr_primes)
  {
    k=0;
    while(primes[k]*primes[k]<=j)
    {
      if(j%primes[k]==0)
      {
        j+=2;
        k=0;
      }
      else
      {
        k++;
      }
    }
    primes[i]=j;
    i++;
    j+=2;
  }
}

void sieve_init(int sieve_size)
{
  int i, j;
  for(i=0;i<32;i++)
  {
    mask1[i]=1<<i;
    mask0[i]=0xFFFFFFFF-mask1[i];
  }
  sieve = sieve_malloc(sieve_size, "sieve");
  sieve_base = sieve_malloc(sieve_size, "sieve_base");

  fill_with_odd_primes(prime_base, SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA);
  
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

int
compute_first_sieve_location(const unsigned long long int k_start, const int p,
                             const unsigned int exp)
{
  int ii,jj, k;
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
    printf("calculation of k_init failed!\n");
    printf("  k_start= %llu\n", k_start);
    printf("  exp= %u\n",exp);
    printf("  ii= %d\n",ii);
    printf("  jj= %d\n",jj);
    printf("  k= %d\n",k);
    printf("  p= %d\n",p);
    printf("  check= %" PRId64 "\n",check);
  }
  
  return k;
}

/**
 * @brief copy <sieve_limit> primes from prime_base[] to primes[] excluding any
primes which divide the exponent itself.
 * 
 * Because factors are 2 * k * <exp> + 1 it is not a good idea to use divisors 
 * of <exp> for sieving. Additionally, primes which are factors of M<exp> are
 * removed. It would be sufficient to add an initial offset for those primes
 * but removing them allows to find composite factors.
 *
 * @param sieve_limit p_sieve_limit: number of primes to put into primes[]
 * @param exp p_exp: the exponent in 2^<exp>-1, the number we're factoring
 */
void
sieve_init_primes(const int exp, const int sieve_limit,
                  const int sieve_base_size)
{
  if (sieve_debugging_output & TRACE_FUNCTION_CALLS) {
    printf("%s(exp=%u, sieve_limit=%d)\n",
           __func__, exp, sieve_limit);
    fflush(stdout);
  }
  int i = 0, j = 0;
  sieve_size_divisors_nr_primes = 0;
  while(i < sieve_limit)
  {
    if(j >= (SIEVE_PRIMES_MAX + SIEVE_PRIMES_EXTRA))
    {
      printf("ERROR: SIEVE_PRIMES_EXTRA is too small, contact the author!\n");
      exit(EXIT_FAILURE);
    }
    const int p = prime_base[j];
    /* Don't sieve by primes that divide the exponent. Since candidate
     * factors are of the form f = k*exp+1, a prime p | exp would always
     * have f % p = 1 and thus cannot divide any candidate divisor, i.e.,
     * it never hits in the sieve at all. Leaving them in would lead to an
     * unsolvable modular inverse when the sieve initialisation code tries
     * to calculate the first location that gets hit. */
    const int divides_exponent = exp % p == 0;

    /* Don't try to sieve by a prime that divides NUM_CLASSES as we consider
     * only candidate divisors in those classes that are coprime to
     * NUM_CLASSES.
     */
    const int divides_NUM_CLASSES = NUM_CLASSES % p == 0;

    /* Primes that divide sieve_base_size are handled separately and
     * should not be sieved by the general code, either.
     */
    const int divides_sieve_base_size = sieve_base_size % p == 0;

    /* If this prime is a factor of 2^exp-1, then we don't use it for
     * sieving so that any factors divisible by this prime are correctly
     * reported. */
    const int is_factor = powmod(2, exp, p) == 1;

    if (divides_exponent && (sieve_debugging_output & TRACE_SKIPPED_PRIMES)) {
      printf("%s():%d Skipping prime %d because it divides the exponent %d\n",
             __func__, __LINE__, p, exp);
    }

    if (divides_NUM_CLASSES && sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
      printf("%s():%d skipping prime %d because it divides "
              "NUM_CLASSES = %d\n", __func__, __LINE__, p, NUM_CLASSES);
    }

    if (divides_sieve_base_size && sieve_debugging_output & TRACE_SKIPPED_PRIMES) {
      printf("%s():%d skipping prime %d because it divides "
              "sieve_base_size = %d\n", __func__, __LINE__, p, sieve_base_size);
    }

    if (is_factor && (sieve_debugging_output & TRACE_SKIPPED_PRIMES)) {
      printf("%s():%d Skipping prime %d because it divides  2^%d-1\n",
             __func__, __LINE__, p, exp);
    }

    if(!divides_exponent && !divides_NUM_CLASSES && 
       !divides_sieve_base_size && !is_factor)
    {
      primes[i++] = p;
    }

    /* Put in sieve_size_divisors_primes the prime factors of sieve_base_size
    * and in sieve_size_divisors_nr_primes their number. We consider only primes
    * that do not divide the exponent, do not divide the number itself, and do
    * not divide NUM_CLASSES.
    * We do it here in sieve_init_primes() because at a later time, maybe we'd
    * like to adjust sieve_base_size depending on the exponent so that exponent
    * and sieve_base_size are coprime.
    */
    if(!divides_exponent && !divides_NUM_CLASSES && 
       divides_sieve_base_size && !is_factor)
    {
      sieve_size_divisors_primes[sieve_size_divisors_nr_primes++] = p;
    }

    j++;
  }
}

void 
sieve_init_class(unsigned int exp, unsigned long long int k_start,
                 int sieve_limit, int sieve_size)
{
  int i,j,p;

  if (sieve_debugging_output & TRACE_FUNCTION_CALLS) {
    printf("%s(exp=%u, k_start=%llu, sieve_limit=%d, sieve_size=%d)\n",
           __func__, exp, k_start, sieve_limit, sieve_size);
    fflush(stdout);
  }

  for(i=0;i<sieve_limit;i++)
  {
    p=primes[i];
    k_init[i] = compute_first_sieve_location(k_start, p, exp);
  }
  
  memset(sieve_base, 0xFF, sieve_size_in_words(sieve_size)*sizeof(unsigned int));
  if (sieve_debugging_output & TRACE_HEXDUMP_SIEVE) {
    printf("%s():%d sieve_base[] = ",  __func__, __LINE__);
    hexdump(sieve_base, 10);
  }

  /* presieve the primes that divide SIEVE_SIZE_DIVISORS in sieve_base */
  for(i = 0; i < sieve_size_divisors_nr_primes; i++)
  {
    p = sieve_size_divisors_primes[i];
    j = compute_first_sieve_location(k_start, p, exp);
    if (sieve_debugging_output & TRACE_K) {
      printf("%s():%d sieving sieve_size_divisors_primes[%d] = <%d, %d>\n",
             __func__, __LINE__, i, p, j);
    }
    while(j<sieve_size)
    {
//if((2 * (exp%p) * ((k_start+j*NUM_CLASSES)%p)) %p != (p-1))printf("EEEK: sieve: p=%d j=%d k=%" PRIu64 "\n",p,j,k_start+j*NUM_CLASSES);
      sieve_clear_bit(sieve_base,j);
      j+=p;
    }
//    k_init[i]=j-sieve_size;
  }

  if (sieve_debugging_output & TRACE_HEXDUMP_SIEVE) {
    printf("%s():%d sieve_base[] = ",  __func__, __LINE__);
    hexdump(sieve_base, 10);
  }
  last_sieve = sieve_size;
}


void sieve_candidates(int ktab_size, unsigned int *ktab, int sieve_limit,
                      int sieve_size)
{
  int i=-1,ii,j,k=0,p,c=0,ic;
  unsigned int s,sieve_table_8,*sieve_table_;
  unsigned int mask; //, index, index_max;
  unsigned int *ptr, *ptr_max;

  if (sieve_debugging_output & TRACE_FUNCTION_CALLS) {
    printf("sieve_candidates(ktab_size=%d, ktab=%p, sieve_limit=%d, sieve_size=%d)\n",
           ktab_size, ktab, sieve_limit, sieve_size);
  }

#ifdef RAW_GPU_BENCH
//  quick hack to "speed up the siever", used for GPU-code benchmarks  
  for(i=0;i<ktab_size;i++)ktab[i]=i;
  return;
#endif  

  if(last_sieve < sieve_size)
  {
    i=last_sieve;
    c=-i;
    goto _ugly_goto_in_siever;
  }

  while(k<ktab_size)
  {
//printf("sieve_candidates(): main loop start\n");
    memcpy(sieve, sieve_base, sieve_size_in_words(sieve_size)*sizeof(unsigned int));

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
      j=k_init[i];
//printf("sieve: %d\n",p);
      for(ii=0; ii<32; ii++)
      {
        mask = mask0[j & 0x1F];
/*
        index = j >> 5;
        index_max = sieve_size >> 5;
        if(index_max + (j & 0x1F) < sieve_size)index_max++;
        while(index < index_max)
        {
          sieve[index] &= mask;
          index += p;
        }
        j+=p;
      }
      j = (index<<5) + ((j-p) & 0x1F);
      while(j>=sieve_size)j-=p;
      j+=p;
      k_init[i]=j-sieve_size;*/

        ptr = &(sieve[j>>5]);
        ptr_max = &(sieve[sieve_size >> 5]);
        if( (j & 0x1F) < (sieve_size & 0x1F))ptr_max++;
        while(ptr < ptr_max) /* inner loop, lets kick out some bits! */
        {
          *ptr &= mask;
          ptr += p;
        }
        j+=p;
      }
      j = ((int)(ptr - sieve)<<5) + ((j-p) & 0x1F); /* D'oh! Pointer arithmetic... but it is faster! */
      j -= sieve_size;
      k_init[i] = j % p;
    }

    if (sieve_debugging_output & TRACE_K) {
      printf("%s(ktab_size = %d):%d k = %d\n", __func__, ktab_size, __LINE__, k);
    }
    for(i=SIEVE_SPLIT;i<sieve_limit;i++)
    {
      p=primes[i];
      j=k_init[i];
      /* printf("sieve: p=%d, k_init[%d]=%d, sieve_size=%d\n",
             p, i, j, sieve_size); */
      while(j<sieve_size)
      {
        sieve_clear_bit(sieve,j);
        j+=p;
      }
      k_init[i]=j-sieve_size;
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
    for(i=0;(i<sieve_size) && (i&0x1F);i++)
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
    for(;i<(sieve_size&0xFFFFFFE0) && k<(ktab_size-33);i+=32)	// thirty-three!!!
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
    for(;i<sieve_size;i++)
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
    c+=sieve_size;
  }
  last_sieve=i;
}
