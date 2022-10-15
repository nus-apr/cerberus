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
int find_sub(char [],char [],int,int);
void rev_sub(char [],int,int);
int main() {
    char s1[100],s2[100];
    scanf("%s %s",s1,s2);
    int l=0,le=0,x;
    while(s2[l]!='\0')
    l++;
    while(s1[le]!='\0')
    le++;
    x=find_sub(s1,s2,0,l);
    while(x<le)
    {
    if(x<0)
    break;
    if(x>=0)
    rev_sub(s1,x,(l+x-1));
    x=find_sub(s1,s2,x+l,l);
    }
    printf("%s",s1);
	return 0;
}
int find_sub(char x[],char y[],int s,int l)//finds substring and returns starting index if found else returns -1
{
    int i,j,c=0;
    for(i=s;i<100-s;i++)
    {
        if(x[i]==y[0])
        {
           c=i;
           for(j=1;j<l;j++)
           {
                
                if(x[++i]!=y[j])
            {
             break; 
            }
            if(j==l-1)
            return c;
           }
        }
    } 
    return -1;
}
void rev_sub(char s[],int a,int b)
{
   char dup[100];
   int i,c=0;
   for(i=b;i>=a;i--)
   dup[c++]=s[i];
   c++;
   c=0;
   for(i=a;i<=b;i++)
   s[i]=dup[c++];
   
}