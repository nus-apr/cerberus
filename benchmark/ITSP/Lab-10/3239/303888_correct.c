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
    int i,flag,mark=1,j;
    for(i=0;i<n;i++)
    {
        flag=0;
     for(j=0;j<n;j++)
     {
         if(*(s1+i)==*(s2+j))
         {
             flag=1;
             break;
         }
     }
     if(flag==0)
     {
         mark=0;
         break;
     }
    }
    return mark;
}

int main(){
    //Fill this area with your code.
    int size1,size2,res;
    char *s1,*s2;
    char ch;
    scanf("%d",&size1);
    s1=(char*)malloc((size1+1)*sizeof(char));
    scanf("%s",s1);
    scanf("%d",&size2);
    s2=(char*)malloc((size2+1)*sizeof(char));
    scanf("%s",s2);
    if(size1!=size2)
    {
        res=0;
    }
    else
    {
        res=valid(s1,s2,size1);
    }
    if(res==1)
    {
        printf("Valid");
    }
    if(res==0)
    {
        printf("Not Valid");
    }
    return 0;
}