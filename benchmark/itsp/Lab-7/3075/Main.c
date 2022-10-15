/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template.
--------------------------------------------------------------------------------------------------------------

Write a program to right circular rotate the given string by an input amount 'n' and print the final string. 

Input Format:
A string of at most 100 characters. There is no whitespace.
A positive integer.	

Output Format:
Rotated string.		
	
Example 1:
Input:
abcdef 
2

Output:
efabcd

Example 2: 
Input:
hello-@programmer 
5

Output:
ammerhello-@progr

*/
#include<stdio.h>

int strLen(char str[]) {
    int i;
    for(i=0;str[i]!='\0';i++){}
        
    return i;    

}

void RotateByAmount (char * str, int amount)	// Circular rotate a string right by amount
{
		int i,pos,len= strLen(str);
		char temp[len];
		for(i=0;i<len;i++)
		{
			temp[i]=str[i];				
		}
		for(i=0;i<len;i++)
		{
			int pos = i+amount;	
			pos=pos%len;			
			str[pos]=temp[i];			
		}
}

int main()
{
	char str[100];
	scanf("%s",str);
	int n;
	scanf("%d",&n);
	RotateByAmount(str,n);
	printf("%s",str);
	return 0;
}