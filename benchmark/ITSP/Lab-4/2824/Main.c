/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Use of character constants instead of ASCII values ('a', 'b, ..., 'A', 'B', ..., '0', '1' etc instead of ASCII values like 65, 66, 48 etc.) 
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

A year is given as input. Write a program to determine whether the year is a leap year or not. A leap year is a year which is divisible by 4 and if it is divisible by 100 then it should also be divisible by 400.

Example: 
Input: 2004
Output: Leap Year 

Input: 1701 
Output: Not Leap Year
*/
#include<stdio.h>

int main()
{
	int y;
	scanf("%d", &y);
	if(y % 4 == 0)
	{
		if(y % 100 == 0)
		{
			if(y % 400 == 0)
				printf("Leap Year");
			else
				printf("Not Leap Year");
		}
		else
			printf("Leap Year");
	}
	else
		printf("Not Leap Year");
	return 0;
	
}