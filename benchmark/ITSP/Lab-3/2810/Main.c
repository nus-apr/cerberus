/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code 
- Indentation: align your code properly 
---------------------------------

Write a C program to calculate the area of the triangle formed by the three points (a,b), (a,0) and (0,b), where the coordinates are float and are given by the user. The output should be in four decimal place. The exact format should be: 

INPUT format: a b are given in a line. 
OUTPUT format: For example, on the input 1 1 the output should be: 

The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000.
*/
#include<stdio.h>

int main(){
	float a,b, a1,b1;
	float area;
	
	scanf("%f %f",&a,&b);
	
	a1=a, b1=b;
	if (a<0) a1=-a;
	if (b<0) b1=-b;
	
	area = 0.5*a1*b1;
	
	printf("The area of (%.4f,%.4f), (%.4f,0) and (0,%.4f) is %.4f.\n", a,b,a,b,area);

	return 0;
}