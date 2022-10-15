/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"1"
Verdict:ACCEPTED, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"2"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"7"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"0"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"2"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"16"
Verdict:ACCEPTED, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"6"
*/
#include <stdio.h>
#include <stdlib.h>

int makeEqual(char * s1, int n1, char * s2, int n2){
    int i,j,c,k;
    c=0;
    for(i=0;i<n1;i++){
        k=0;
        for(j=0;j<n2;j++){
            if(*(s1+i)==*(s2+j)){
                *(s2+j)=0;
                k=1;
                break;
            }
        }
        if(k==1)
        c=c+1;
    }
    return c;
}

int main(){
    int n1,n2;//declarations
    scanf("%d",&n1);//scaning n
    char*s,*r,*copy;//pointers to strings
    s=(char*)malloc(n1*sizeof(char));
    r=(char*)malloc(n2*sizeof(char));
    copy=(char*)malloc(n2*sizeof(char));

    scanf("%s",s);
    scanf("%d",&n2);
    scanf("%s",r);
    int i;
    for(i=0;i<n2;i++){
        *(copy+i)=*(r+i);
    }
    int n,m;
    n=n1-makeEqual(s,n1,r,n2);
    m=n2-makeEqual(copy,n2,s,n1);
    printf("%d",n+m);
    return 0;
}