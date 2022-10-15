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

int valid(char * s1, char * s2, int n){
  int i,j,count=0;
  for(i=0;i<n;i++)
  {
      int r=0;
      for(j=0;j<n;j++)
      {
          if(*(s1+i)==*(s2+j))
            count++;
            r++;
            if(r>=1)
            break;
      }
  }
  return count;
}

int main(){
    int n1,n2; //Fill this area with your code.
    char *s1,*s2;
    scanf("%d",&n1);
    char a[n1+1];
    scanf("%s",a);
    scanf("%d",&n2);
    char b[n2+1];
    scanf("%s",b);
    if(n1==n2)
    {
        int n=n1,i;
        s1=(char*)malloc((n+1)*sizeof(char));
        s2=(char*)malloc((n+1)*sizeof(char));
        for(i=0;i<=n;i++)
        {
            *(s1+i)=a[i];
            *(s2+i)=b[i];
        }
        if(valid(s1,s2,n)==n)
        printf("Valid");
        else
        printf("Not Valid");
    }
    else
    printf("Not Valid");
    
    return 0;
}