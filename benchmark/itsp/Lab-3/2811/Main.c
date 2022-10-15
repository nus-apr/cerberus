/*
Write a C program to calculate the intersection point of two lines. All the values are in float. 

INPUT: $a_1 \: b_1\: a_2\: b_2$ are given in a line. They specify the two lines $(a_1 X + b_1 Y \,=\, 1 )$ & $(a_2 X + b_2 Y \,=\, 1 )$ .

OUTPUT: If there is no intersection then print "INF" else print the intersection point up to 3 decimal places.

Example 1: On input: 1 0 0 1
OUTPUT: (1.000,1.000)

Example 2: On input: 1 0 1 0
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
	    a = (b2-b1)/d;
	    b = (a1-a2)/d; 
	    printf("(%.3f,%.3f)\n", a,b);
    
	}    
	
	return 0;
}