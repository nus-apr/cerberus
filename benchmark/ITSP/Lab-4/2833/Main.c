/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments for non trivial code 
- Indentation: align your code properly 
- Use of character constants instead of ASCII values ('a', 'b, ..., 'A', 'B', ..., '0', '1' etc instead of ASCII values like 65, 66, 48 etc.

You are given a natural number N as input. You need to calculate the number of triangles with integral sides which can be formed with side lengths less than or equal to N.

Input:
4

Output:
Number of possible triangles is 13
*/
#include <stdio.h>
int main() {

	int N;
	int a, b, c , count = 0;

	scanf("%d",&N);

	for(a = 1 ; a <= N ; a++)
		for(b = 1 ; b <= a ; b++)
			for(c =1 ; c <= b ; c++)
				if ( a + b > c && b + c > a && c + a > b)
					count++;


	printf("Number of possible triangles is %d" , count);

	return 0;
}