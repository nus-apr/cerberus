/*numPass=3, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"eag"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"gafh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"ycxz"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"xeaablm"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"sabpqrt"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"sprrr"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"yabcdxz"
*/
#include <stdio.h>
#include <stdlib.h>
void sort(char* st,int len)
{
    int a,b;
    for(a=0;a<len;a++)
    {
        int pos=a;
        char sm=*(st+a);
        for(b=a+1;b<len;b++)
        {
            if(*(st+b)<*(st+a))
            {
                sm=*(st+b);
                pos=b;
            }
        }
        char temp=*(st+a);
        *(st+a)=sm;
        *(st+pos)=temp;
    }
}
int main(){
    //Fill this area with your code.
    int l1,a,b;
    scanf("%d",&l1);
    char *st=(char*)malloc((l1+1)*sizeof(char));
    char *copy=(char*)malloc((l1+1)*sizeof(char));
    scanf("%s",st);
    //printf("%s",ch);
    for(a=0;a<l1;a++)
     *(copy+a)=*(st+a);
    //printf("%s\n",copy);
    int cn=1;
    for(a=l1-1;a>0;a--)
    {
       
        for(b=a-1;b>=0;b--)
        {
            if(*(copy+b)<*(copy+a))
            {
                char temp=*(copy+b);
                *(copy+b)=*(copy+a);
                *(copy+a)=temp;
                sort(copy+b+1,l1-b-1);
                cn=0;
                break;
            }
            if(cn==0) break;
        }
    }
    
    if(cn==0)
     printf("%s",copy);
    else
     printf("No Answer");
    
    return 0;
}