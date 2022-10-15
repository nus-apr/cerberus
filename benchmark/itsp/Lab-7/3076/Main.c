/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template.
--------------------------------------------------------------------------------------------------------------

Write a program to swap the first-half with the second-half of the given string, and print the final string. 

Input Format:
A string of at most 100 characters. There is no whitespace.

Output Format:
Transformed string.		
	
Example 1:
Input:
abcdef 

Output:
defabc

Example 2: 
Input:
hello-@programmer 

Output:
ogrammerrhello-@p

*/
#include<stdio.h>

int strLen(char str[]) {
    int i;
    for(i=0;str[i]!='\0';i++){}
        
    return i;    

}


void swapStr (char str[])	// swap the two halves
{
		int i, len= strLen(str);
		char temp;
		
		for(i=0;i<len/2;i++)
		{
			temp = str[i];
			str[i] = str[(len+1)/2 + i];
			str[(len+1)/2 + i] = temp;			
		}
}

int main()
{
	char str[100];
	scanf("%s",str);
	int n;
	scanf("%d",&n);
	swapStr(str);
	printf("%s",str);
	return 0;
}