/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template. --------------------------------------------------------------------------------------------------------------

Write a program to shift a given string using the following encoding: 'a' should be shifted by 1, `b' should be shifted by 2 ,....., `z' should be shifted by 26. Print the final string. The string has only lower case alphabets.

Input Format:
A string of at most 100 lower case alphabets.	

Output Format:
The string with each alphabet shifted appropriately.

Example 1:
Input:	
abcdef 

Output:	
bdfhjl

Example 2:
Input: 
wxyz

Output:
tvxz
*/
#include<stdio.h>

int strLen(char str[]) {
    int i;
    for(i=0;str[i]!='\0';i++){}
        
    return i;    

}

void Shift(char str[])	 
{
		int i,len= strLen(str);
		
		for(i=0;i<len;i++)
		    str[i] = (2*(str[i]-'a')+1)%26 + 'a';	
		
}
int main()
{
	char str[100];
	scanf("%s",str);
	
	Shift(str);
	printf("%s",str);
	return 0;
}