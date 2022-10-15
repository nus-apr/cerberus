/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template. --------------------------------------------------------------------------------------------------------------

Write a program that inserts another substring s2 before the first occurrence of a given character c1 in a given primary string s1.

Input Format:
A string s1 of at most 50 characters. There is no whitespace. 
A character c1. 
A string s2 of at most 50 characters. There is no whitespace.

Output Format:
Primary-string after modification if any.

Example 1:
Input:
abcxy
b
hi

Output:
ahibcxy

Example 2:
Input:
jhggd 
g 
sdfghjk

Output:
jhsdfghjkggd
*/
#include<stdio.h>

int length(char *s)
{
	int i=0;
	while(s[i]!='\0')
	{
		i++;
	}
	return i;
}

void Insert(char *str, char *sub, int pos)
{
	int i=-1;
	int len = length(str);
	char temp[100];
	do
	{
		i++;
		temp[i]=str[i];
	}while(i!=len);
	
	int sublen=length(sub);
	int j = pos;
	
	for(i=0;i<sublen;i++)
	{
		str[j++]=sub[i];
	}
	
	for(i=pos;i<=len;i++)
	{
		str[j++]=temp[i];
	}
}

//returns the position of a in str
int charCheck (char * str , char a ,int i )
{
	if(str[i]==a)
			return i;
	else 
		return -1;
	
}

int main()
{

    char str[100];


    int i =-1,start=0;

    scanf("%s",str);

    char c1;
    scanf("\n%c",&c1); 
 
    char subs1[50];
    scanf("%s",subs1);


    for(i=0;i<length(str);i++)
    {
	    int val=charCheck(str,c1,i);
	    if(val>=0) 
	    {
		    start=i;
		
    		Insert(str,subs1,start);
	    	break;
	    }

    }

    printf("%s",str);

    return 0;
}