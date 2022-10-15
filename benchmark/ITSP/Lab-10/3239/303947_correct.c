/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde
5
dceab", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:1, Input:"5
xatps
5
sptay", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
7
balmaex", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:1, Input:"5
hello
5
lolhe", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:0, Input:"5
hello
7
labexam", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
anagram
6
anagrm", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"6
pppqqq
6
qpqpqp", ExpOutput:"Valid", Output:"Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
abcdefg
7
gfedbac", ExpOutput:"Valid", Output:"Valid"
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
      int r=0;          //this is for the check on multiple repetitions                           of an element
      for(j=0;j<n;j++)
      {
          if(*(s1+i)==*(s2+j))
          {
            count++;   //this is to see the no. of matches
            r++;
            if(r>=1) //since check is element by element
            break;
          }
      }
  }
  return count;
}


int main(){
    int n1,n2;     //take inputs
    char *s1,*s2;
    scanf("%d",&n1);
    s1=(char*)malloc((n1+1)*sizeof(char));
    scanf("%s",s1);
    scanf("%d",&n2);
    s2=(char*)malloc((n2+1)*sizeof(char));
    scanf("%s",s2);
    if(n1==n2)  //proceed only if the string lengths given a sinput are                   equal
    {
        int n=n1,i;
        if(valid(s1,s2,n)==n) 
        printf("Valid");
        else
        printf("Not Valid");
    }
    else
    printf("Not Valid");
    
    return 0;
}