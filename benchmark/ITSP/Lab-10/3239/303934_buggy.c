/*numPass=7, numTotal=9
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
hello
7
labexam", ExpOutput:"Not Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
anagram
6
anagrm", ExpOutput:"Not Valid", Output:""
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
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<n;j++)
        {
            if(s1[i]==s2[j])
            {
                s2[j]='A';
                flag=1;
                break;
            }
        }
        if(!flag)
        {
            return 0;
        }
    }
    return 1;
}

int main(){
    int n,m;
    char *a,*b;
    scanf("%d",&n);
    a=(char *)malloc((n+1)*sizeof(char));
    scanf("%s",a);
    scanf("%d",&m);
    if(n!=m)
    {
        return 0;
    }
    b=(char*)malloc((m+1)*sizeof(char));
    scanf("%s",b);
    if(valid(a,b,n))
    {
        printf("Valid");
    }
    else
    {
        printf("Not Valid");
    }
    free(a);
    free(b);
    return 0;
}