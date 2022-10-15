/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>
int less_than_n(char a[],int n,char c)
{
    int i=0,count=0;
    while((a[i]!='\0')&&(count<n))
    {
        if(c==a[i])
        {
            count++;
        }
        i++;
    }
    if(count==n)
    return 0;   //if statement is false
    else 
    return 1;   //if statement is true
}
int search(char s1[],char s2[])
{
    int i=0,j=0;
    while(s1[i]!='\0')
    {
        if(s1[i]==s2[j])
        {
            j++;
            if(s2[j]=='\0')
               {
                  j=-1;
                  break;
               }
            if(s1[i+1]!=s2[j])
               {
                  j=0;
               }
        }
        i++;
    }
    if(j==-1)
    {
       return 1;
    }
    else
    {
       return 0;
    }
}
int main() 
{
	char s1[101],s2[101],c;
	int n;
	scanf("%s %c %d %s",s1,&c,&n,s2);
	if(((search(s1,s2)==0)&&(less_than_n(s1,n,c)==1))||((search(s1,s2)==1)&&(less_than_n(s1,n,c)==0)))
	{
	   printf("YES");
	}   
	else
	{
	   printf("NO");
	}   
	return 0;
}