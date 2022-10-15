/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde
5
dceab", ExpOutput:"Valid", Output:"Valid"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
xatps
5
sptay", ExpOutput:"Not Valid", Output:"Invalid"
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
int c[256];
int valid(char * s1, char * s2, int n){
    int i;
    for(i=0;i<n;i++)
       c[s1[i]]++; 
    
    for(i=0;i<n;i++)
       c[s2[i]]--;
    
    for(i=0;i<256;i++)
      if(c[i]!=0)
        return 0;
      else 
        continue;
    return 1;    
}

int main(){
    char *s1,*s2;
    
    int n1,n2;
    scanf("%d\n",&n1);
    s1=(char*)malloc(sizeof(char)*(n1+1));
    scanf("%s\n",s1);
    scanf("%d\n",&n2);
    s2=(char*)malloc(sizeof(char)*(n2+1));
    scanf("%s",s2);
    if(n1==n2)
    printf("%s",valid(s1,s2,n2)?"Valid":"Invalid");
    else 
    printf("Not Valid");
    return 0;
}