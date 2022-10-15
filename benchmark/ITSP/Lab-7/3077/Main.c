/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template. --------------------------------------------------------------------------------------------------------------

Write a program to shift a given string by an input amount 'n' and print the final string. The string has only lower case alphabets.

Input Format:
A string of at most 100 lower case alphabets.	
A non-negative integer n.

Output Format:
The string with each alphabet shifted by n.

Example 1:
Input:	
abcdef 
2

Output:	
cdefgh

Example 2:
Input: 
wxyz
3

Output:
zabc
*/
#include<stdio.h>

int strLen(char str[]) {
    int i;
    for(i=0;str[i]!='\0';i++){}
        
    return i;    

}

void ShiftByAmount (char * str, int amount)	 // Shift all characters by a specified amount
{
		int i,len= strLen(str);
		
		for(i=0;i<len;i++)
		    str[i]=(str[i]-'a'+amount)%26 + 'a';	
		
}
int main()
{
	char str[100];
	scanf("%s",str);
	int n;
	scanf("%d",&n);
	ShiftByAmount(str,n);
	printf("%s",str);
	return 0;
}