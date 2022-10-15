/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code 
- Indentation: align your code properly 
---------------------------------

Write a C program to output the sign of an input float number. On input $a$ you have to output positive, zero or negative.

INPUT format: a
OUTPUT format: input is zero. OR a is positive/negative. Use 4 decimal places.

Example 1: On input -12,
OUTPUT: -12.0000 is negative. 

Example 2: On input 0,
OUTPUT: input is zero.

Example 3: On input 1,
OUTPUT: 1.0000 is positive.
 
*/
#include<stdio.h>

int main(){
	float a;
	
	scanf("%f",&a);
	
	if (a<0) printf("%.4f is negative",a);
	if (a==0) printf("input is zero");
	if (a>0) printf("%.4f is positive",a);
	
	return 0;
}