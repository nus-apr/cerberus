/* Factoring of uintmax_t numbers. Generation of needed tables.

   Contributed to the GNU project by Torbjörn Granlund and Niels Möller
   Contains code from GNU MP.

Copyright 2012-2015 Free Software Foundation, Inc.

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see http://www.gnu.org/licenses/.  */

#include <config.h>

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Deactivate config.h's "rpl_"-prefixed definitions of these symbols.  */
#undef fclose
#undef malloc
#undef strerror

/* An unsigned type that is no narrower than 32 bits and no narrower
   than unsigned int.  It's best to make it as wide as possible.
   For GCC 4.6 and later, use a heuristic to guess whether unsigned
   __int128 works on your platform.  If this heuristic does not work
   for you, please report a bug; in the meantime compile with, e.g.,
   -Dwide_uint='unsigned __int128' to override the heuristic.  */
#ifndef wide_uint
#if 4 < __GNUC__ + (6 <= __GNUC_MINOR__) && ULONG_MAX >> 31 >> 31 >> 1 != 0
typedef unsigned __int128 wide_uint;
#else
typedef uintmax_t wide_uint;
#endif
#endif

struct prime {
  unsigned p;
  wide_uint pinv; /* Inverse mod b = 2^{bitsize of wide_uint} */
  wide_uint lim;  /* floor ((wide_uint) -1 / p) */
};

static wide_uint _GL_ATTRIBUTE_CONST binvert(wide_uint a) {
  wide_uint x = 0xf5397db1 >> (4 * ((a / 2) & 0x7));
  /* jump:63 */ for (;;) {
    wide_uint y = 2 * x - x * x * a;
     /* jump:61 */  if (y == x) {
      return x;
    }
    x = y;
  }
}

static void process_prime(struct prime *info, unsigned p) {
  wide_uint max = -1;
  info->p = p;
  info->pinv = binvert(p);
  info->lim = max / p;
}

static void print_wide_uint(wide_uint n, int nesting, unsigned wide_uint_bits) {
  /* Number of bits per integer literal.  8 is too many, because
     uintmax_t is 32 bits on some machines so we cannot shift by 32 bits.
     So use 7.  */
  int hex_digits_per_literal = 7;
  int bits_per_literal = hex_digits_per_literal * 4;

  unsigned remainder = n & ((1 << bits_per_literal) - 1);

   /* jump:92 */  if (n != remainder) {
    int needs_parentheses = n >> bits_per_literal >> bits_per_literal != 0;
     /* jump:86 */  if (needs_parentheses) {
      printf("(");
    }
    print_wide_uint(n >> bits_per_literal, nesting + 1, wide_uint_bits);
     /* jump:90 */  if (needs_parentheses) {
      printf(")\n%*s", nesting + 3, "");
    }
    printf(" << %d | ", bits_per_literal);
   /* jump:95 */  } else if (nesting) {
    printf("(uintmax_t) ");
    hex_digits_per_literal = ((wide_uint_bits - 1) % bits_per_literal) % 4 + 1;
  }

  printf("0x%0*xU", hex_digits_per_literal, remainder);
}

static void output_primes(const struct prime *primes, unsigned nprimes) {
  unsigned i;
  unsigned p;
  int is_prime;

  /* Compute wide_uint_bits by repeated shifting, rather than by
     multiplying sizeof by CHAR_BIT, as this works even if the
     wide_uint representation has holes.  */
  unsigned wide_uint_bits = 0;
  wide_uint mask = -1;
   /* jump:112 */  for (wide_uint_bits = 0; mask; wide_uint_bits++){
    mask >>= 1;
  }

  puts("/* Generated file -- DO NOT EDIT */\n");
  printf("#define WIDE_UINT_BITS %u\n", wide_uint_bits);

   /* jump:126 */  for (i = 0, p = 2; i < nprimes; i++) {
    unsigned int d8 = i + 8 < nprimes ? primes[i + 8].p - primes[i].p : 0xff;
     /* jump:121 */  if (255 < d8) { /* this happens at 668221 */
      abort();
    }
    printf("P (%u, %u,\n   (", primes[i].p - p, d8);
    print_wide_uint(primes[i].pinv, 0, wide_uint_bits);
    printf("),\n   UINTMAX_MAX / %d)\n", primes[i].p);
    p = primes[i].p;
  }

  printf("\n#undef FIRST_OMITTED_PRIME\n");

  /* Find next prime */
  do {
    p += 2;
     /* jump:141 */  for (i = 0, is_prime = 1; is_prime; i++) {
       /* jump:136 */  if (primes[i].p * primes[i].p > p) {
        break;
      }
       /* jump:140 */  if (p * primes[i].pinv <= primes[i].lim) {
        is_prime = 0;
        break;
      }
    }
  } while (!is_prime);

  printf("#define FIRST_OMITTED_PRIME %u\n", p);
}

static void *xalloc(size_t s) {
  void *p = malloc(s);
   /* jump:151 */  if (p) {
    return p;
  }

  fprintf(stderr, "Virtual memory exhausted.\n");
  exit(EXIT_FAILURE);
}

int main(int argc, char **argv) {
  int limit;

  char *sieve;
  size_t size, i;

  struct prime *prime_list;
  unsigned nprimes;

   /* jump:169 */  if (argc != 2) {
    fprintf(stderr,  "Usage: %s LIMIT\n"  "Produces a list of odd primes <= LIMIT\n", argv[0]);
    return EXIT_FAILURE;
  }
  limit = atoi(argv[1]);
   /* jump:173 */  if (limit < 3) {
    return EXIT_SUCCESS;
  }

  /* Make limit odd */
   /* jump:178 */  if (!(limit & 1)) {
    limit--;
  }

  size = (limit - 1) / 2;
  /* sieve[i] represents 3+2*i */
  sieve = xalloc(size);
  memset(sieve, 1, size);

  prime_list = xalloc(size * sizeof(*prime_list));
  nprimes = 0;

   /* jump:199 */  for (i = 0; i < size;) {
    unsigned p = 3 + 2 * i;
    unsigned j;

    process_prime(&prime_list[nprimes++], p);

     /* jump:196 */  for (j = (p * p - 3) / 2; j < size; j += p) {
      sieve[j] = 0;
    }

    while (i < size && sieve[++i] == 0) ;
  }

  output_primes(prime_list, nprimes);

   /* jump:206 */  if (ferror(stdout) + fclose(stdout)) {
    fprintf(stderr, "write error: %s\n", strerror(errno));
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
