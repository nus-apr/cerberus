/*numPass=2, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"aae"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"aagf"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"ccyx"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"labexaam"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"abbqrsp"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"prrrrs"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"abdccyx"
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
            *(s+i+1)=temp;
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