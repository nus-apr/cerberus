/* Test mpz_gcd, mpz_gcdext, and mpz_gcd_ui.

Copyright 1991, 1993, 1994, 1996, 1997, 2000, 2001, 2002, 2003, 2004, 2005,
2008, 2009 Free Software Foundation, Inc.

This file is part of the GNU MP Library.

The GNU MP Library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

The GNU MP Library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the GNU MP Library.  If not, see http://www.gnu.org/licenses/.  */

#include <stdio.h>
#include <stdlib.h>

#include "gmp.h"
#include "gmp-impl.h"
#include <klee/klee.h>
#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

/* Keep one_test's variables global, so that we don't need
   to reinitialize them for each test.  */

void print_info(mpz_t op1, mpz_t op2, mpz_t gcd, mpz_t s, mpz_t t){
	printf("gcd =  (s*op1 + t*op2)\n");
	printf("op1:");
	mpz_out_str(stdout, 16, op1);
	printf("\t");
	printf("op2:");
	mpz_out_str(stdout, 16, op2);
	printf("\t");
	printf("gcd:");
	mpz_out_str(stdout, 16, gcd);
	printf("\t");
	printf("s:");
	mpz_out_str(stdout, 16, s);
	printf("\t");
	printf("t:");
	mpz_out_str(stdout, 16, t);
	printf("\n");
}

void test(const char * s1, const char * s2, mpz_t op1, mpz_t op2, mpz_t gcd, mpz_t s, mpz_t t){
  mpz_set_str(op1, s1,16);
  mpz_set_str(op2, s2,16);
  //a*s + b*t = g -> mpz(g,s,t,a(inp),b(inp))
  mpz_gcdext(gcd, s,t, op1, op2);
  TRIDENT_OUTPUT("obs", "i32", mpz_sgn(gcd));
  print_info(op1, op2, gcd, s, t);
	
}

int
main (int argc, char **argv)
{
  mpz_t op1;
  mpz_t op2;
  mpz_t gcd, s,t;
  char* filename = argv[1];
  mpz_inits(op1, op2, gcd,s,t, 0);
  //BINARY GCD TEST
  char line1 [1000];
 char line2 [1000];
FILE *file = fopen ( filename, "r" );
if (file != NULL) { fgets(line1,sizeof line1,file);  fgets(line2,sizeof line2,file); fclose(file);  }
else {    perror(filename); }

  test(line1,line2, op1, op2, gcd, s, t);
  //test("1", "-1",op1, op2, gcd, s, t);
 //test("60", "30",op1, op2, gcd, s, t);
  
  //test("34", "-4", op1, op2, gcd, s, t);
  //test("300300300300300300","900900900900900900", op1, op2, gcd, s, t);
  mpz_clears(op1, op2, gcd,s,t,0);
  exit (0);
}


