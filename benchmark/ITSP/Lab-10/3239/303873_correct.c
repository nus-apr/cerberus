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
int valid(char * s1,int n, char * s2, int m){
    if(n!=m)return 0;
    int count[26],i;
    for(i=0;i<26;i++){
        count[i]=0;
    }
    for(i=0;i<n;i++){
        count[*(s1+i)-97]+=1;
    }
    for(i=0;i<m;i++){
        count[*(s2+i)-97]-=1;
    }
    for(i=0;i<26;i++){
        if(count[i]!=0)return 0;
    }
    return 1;
}

int main(){
    int n,m;
    scanf("%d\n",&n);
    char *a=(char*)malloc((n+1)*sizeof(char));
    scanf("%s",a);
    scanf("%d\n",&m);
    char *b=(char*)malloc((m+1)*sizeof(char));
    scanf("%s",b);
    (valid(a,n,b,m)==1)?printf("Valid"):printf("Not Valid");
    free(a);
    free(b);
    return 0;
}