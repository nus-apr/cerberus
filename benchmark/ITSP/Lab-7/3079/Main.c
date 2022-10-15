/*
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for nontrivial code 
- Indentation: align your code properly 
- Function use and modular programming 
- Usage of string.h is NOT allowed. Do not include anything in the header other than what is already given in the template.
--------------------------------------------------------------------------------------------------------------

Write a program that, in place, reverses the occurrence of a given substring 's2' in the primary string 's1'. Print the final string.

Input Format:
A string s1 of at most 100 characters. There is no whitespace.
A string s2 of at most 100 characters. There is no whitespace.

Output Format
Primary-string after modification if any.

Example 1:
Input:
abcde
bcd

Output:
adcbe

Example 2:
Input:
abcde
acb

Output:
abcde

Example 3:
Input:
abcdebcd 
bcd

Output:
adcbedcb
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

void ReverseString ( char * str, int start , int end)		// reverses string between start and end positions
{
	int i=start;
	int j=end;
	int temp;
	while(i<j)
	{
		temp=str[i];
		str[i]=str[j];
		str[j]=temp;
		i++;
		j--;
	}
}

//returns the end point of the sub inside str
int substrCheck(char* str,char *sub,int start)
{
	int i=start,j=0;
	int flag=0;
	int len = length(str);
	int lensub = length(sub);

	if(start+lensub<=len)
	{	
		flag=1;
		for(j=0;j<length(sub);j++)
		{
			if(str[i+j]!=sub[j])
			{
				flag=0;
				
			}
		}
	}

    if(flag==1)
	    return start+lensub-1;
    else
	return -1;
}
	

int main()
{

    char s1[100];


    int i =-1,start=0,end=0;

    scanf("%s",s1);

    char s2[100];
    scanf("%s",s2);



    for(i=0;i<length(s1);i++)
    {
	    int val=substrCheck(s1,s2,i);
	    if(val>=0) 
	    {
		    start=i;
		    end=val;
		    ReverseString(s1,start,end);
		    i=end;
	    }

    }

    printf("%s",s1);

    return 0;
}