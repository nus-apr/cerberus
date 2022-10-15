/*numPass=4, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
abcde
5
dceab", ExpOutput:"Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:1, Input:"5
xatps
5
sptay", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmaex", ExpOutput:"Valid", Output:"Not Valid"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
hello
5
lolhe", ExpOutput:"Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"5
hello
7
labexam", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
anagram
6
anagrm", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
pppqqq
6
qpqpqp", ExpOutput:"Valid", Output:"Not Valid"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abcdefg
7
gfedbac", ExpOutput:"Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"1 
p
1 
p", ExpOutput:"Valid", Output:"Valid"
*/
#include <stdio.h>
#include <stdlib.h>
int valid(char * s1, char * s2, int n)
{
    int i,j,k=0;
    for(i=0;i<n;i++)
    {
        for(j=0;j<n;j++)
        {
           if(s1[i]==s2[j])
           {
             k=k+1;  
             continue;  
           }
           if(k==n)
           {
             break;  
           }
        }
           if(k==n);
           {
             break;
           }
    }
    
    if(k==n)
    {
      return 1;    
    }
    
    if(k!=n)
    {
      return 2;    
    }
    
}

int main()
{
    int n,m;
    char *s1,*s2;
     s1 = (char*)malloc((n+1)*sizeof(char));
    s2 = (char*)malloc((n+1)*sizeof(char));
    scanf("%d",&n);
    scanf("%s",s1);
    scanf("%d",&m);
    scanf("%s",s2);
    
    if((n==m)&&(valid(s1,s2,n)==1))
    {
      printf("Valid");
    }
    else
    {
      printf("Not Valid");    
    }
    return 0;
}