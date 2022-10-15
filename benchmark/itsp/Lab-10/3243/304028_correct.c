/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"eag"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"fagh"
Verdict:ACCEPTED, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"xcyz"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"labexma"
Verdict:ACCEPTED, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"apbqrst"
Verdict:ACCEPTED, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"prrsr"
Verdict:ACCEPTED, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"abdxcyz"
*/
#include <stdio.h>
#include <stdlib.h>
void lexo(char *s,int n)
{
    int i,j,k;
    char temp,*s2;
    s2=(char*)malloc(n*sizeof(char));
    for(i=(n-1);i>0;i--)
    {
        if(*(s+i)>*(s+i-1))
        {
            j=i;
            temp=*(s+i);
            *(s+i)=*(s+i-1);
            *(s+i-1)=temp;
            break;
        }
        else
        {
            temp=*(s+i);
            *(s+i)=*(s+i-1);
            *(s+i-1)=temp;
        }
    }
    if(i==0)
    {
        printf("No Answer");
        return;
    }
    else
    {
        for(k=0;k<(n-i-1);k++)
        {
            *(s2+k)=*(s+i+k+1);
        }
        for(k=0;k<(n-i-1);k++)
        {
            *(s+i+1+k)=*(s2+n-i-1-1-k);
        }
    }
        printf("%s",s);
}
int main()
{
    int n;
    char *st;
    scanf("%d",&n);
    st=(char*)malloc((n+1)*sizeof(char));
    *(st+1)='\0';
    scanf("%s",st);
    lexo(st,n);
    return 0;
}