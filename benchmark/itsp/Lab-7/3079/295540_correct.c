/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcde 
bcd ", ExpOutput:"adcbe", Output:"adcbe"
Verdict:ACCEPTED, Visibility:1, Input:"abcde 
acb ", ExpOutput:"abcde", Output:"abcde"
Verdict:ACCEPTED, Visibility:1, Input:"abcdebcd 
bcd ", ExpOutput:"adcbedcb", Output:"adcbedcb"
Verdict:ACCEPTED, Visibility:1, Input:"qwerty
t", ExpOutput:"qwerty", Output:"qwerty"
Verdict:ACCEPTED, Visibility:0, Input:"manually
all", ExpOutput:"manullay", Output:"manullay"
Verdict:ACCEPTED, Visibility:0, Input:"iamesrever
esrever", ExpOutput:"iamreverse", Output:"iamreverse"
Verdict:ACCEPTED, Visibility:0, Input:"youdogaredog
dog", ExpOutput:"yougodaregod", Output:"yougodaregod"
Verdict:ACCEPTED, Visibility:0, Input:"ghhghghhghghhg
hhg", ExpOutput:"gghhhgghhhgghh", Output:"gghhhgghhhgghh"
*/
#include <stdio.h>
char a[100],b[100];
int n1,n2;
int length(char a[]);
int compare(int i);
void replace(int n,char c[]);
int main() {
	int i=0,j;
	scanf("%s",a);
	scanf("%s",b);
	n1=length(a);
	n2=length(b);
	
	char c[n2];
    for(i=0;i<n2;i++)
	{
	    c[n2-1-i]=b[i];
	}
	for(i=0;i<=n1;i++)
	{
	    if(a[i]==b[0])
	    {
	    j=compare(i);
	    if(j==1)
	    {
	     replace(i,c);
	     i=i+n2;
	    }
	    }
	}
	printf("%s",a);
	return 0;
}
int length(char a[])
{
    int i;
    for(i=0;i<=100;i++)
    {
        if(a[i]=='\0')
        break;
    }
    return i;
}
int compare(int i)
{
    int k,j;
    k=i;
	for(j=0;j<n2;j++)
	{
	   if(b[j]!=a[k])
	   {
	    return 0;
	   }
	   k++;
	}
	return 1;
}
void replace(int n,char c[])
{
    int i,d=0;
    for(i=n;i<n+n2;i++)
    {
        a[i]=c[d];
        d++;
    }
}