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
    int flag=0;
    for(int i=0;i<n;i++)    {
        for(int j=0;j<n;j++)    {
            if(*(s1+i)==*(s2+j))
            {   flag++;
                *(s2+j)=9;
            }
                
        }
    }
    /*for(int k=0;k<n;k++)
        if(*(s1+k)!='0')
            flag=0;
*/   
    return flag;
}

int main(){
    //Fill this area with your code.
    char *s1,*s2;
    int m,n,flag;
    scanf("%d\n",&m);
    s1=(char *)malloc(m*sizeof(char));
    scanf("%s\n",s1);
    scanf("%d\n",&n);
    s2=(char *)malloc(n*sizeof(char));
    scanf("%s",s2);

    flag=valid(s1,s2,n);
    if(flag==n)
        printf("Valid");
    else
        printf("Not Valid");
   
    free(s1);
    free(s2);
    return 0;
}