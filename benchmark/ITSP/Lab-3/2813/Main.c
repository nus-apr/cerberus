/*
Write a C program to calculate the intersection point of two lines. All the values are in float. 

INPUT: $a_1 \: b_1\: a_2\: b_2$ are given in a line. They specify the two lines $(\frac{X}{a_1} + \frac{Y}{b_1}  \,=\, 1 )$ & $(\frac{X}{a_2} + \frac{Y}{b_2} \,=\, 1 )$ .

OUTPUT: If there is no intersection then print "INF" else print the intersection point up to 3 decimal places.

Example 1: On input: 1 1 1 0.5
OUTPUT: (1.000,0.000)

Example 2: On input: 1 0 0 1
OUTPUT: (0.000,0.000)

Example 3: On input: 1 0 1 0
OUTPUT: INF
*/
#include<stdio.h>

int main(){
	float a1,b1, a2,b2;
	float d,a,b;
	
	scanf("%f %f %f %f",&a1,&b1,&a2,&b2);
	
	d = a1*b2 - a2*b1;
	
	if (d==0) 
	    printf("INF\n");
	else {
	    a = ((b2-b1)/d)*a1*a2;
	    b = ((a1-a2)/d)*b1*b2; 
	    printf("(%.3f,%.3f)\n", a,b);
    
	}    
	
	return 0;
}