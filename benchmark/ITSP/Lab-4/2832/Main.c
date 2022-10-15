/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments for non trivial code 
- Indentation: align your code properly 
- Use of character constants instead of ASCII values ('a', 'b, ..., 'A', 'B', ..., '0', '1' etc instead of ASCII values like 65, 66, 48 etc.

You would be given three integers as input which corresponds to the three sides of a triangle. Write a program to determine if the triangle is acute, right or obtuse. You should print "Invalid Triangle" if the side combinations do not correspond to a valid triangle.

Input:
3 5 4
Output:
Right Triangle
*/
#include <stdio.h>

int main() {

	int a ,b , c , t;
	scanf("%d%d%d" , &a , &b , &c); 

	if (a > c)  //swap a & c
	{	t = c;
		c = a;
		a = t;
	}

	if (b > c)  //swap b & c
	{
		t = c;
		c = b;
		b = t;
	}
	// now c is the longest side

	if ( a + b <= c || b + c <= a || a + c <= b)
		printf("Invalid Triangle");

	else if (c*c > a*a + b*b)
		printf("Obtuse Triangle");

	else if (c*c < a*a + b*b)
		printf("Acute Triangle");

	else
		printf("Right Triangle");

	
	return 0;
}