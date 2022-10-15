/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"-1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"5"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"4"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"-2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"14"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"4"
*/
#include <stdio.h>
#include <stdlib.h>
int n1,n2;
int makeEqual(char * s1, int n1, char * s2, int n2){
    int i,j,k,l,m=0;
    char *c;
    int count=0;
    for(i=0;i<=n1;i++)
    {
        for(j=0;j<=n2;j++)
        {
            if(s1[i]==s2[j])
            {
                count++;
                s2[j]=1;
                break;
            }
        }
    }
    return ((n1+n2)-2*count);
}

int main(){
    char* s1;
    char* s2;
    
   
    scanf("%d",&n1);
    s1=(char*)malloc((n1+1)*sizeof(char));
    scanf("%s",s1);
    scanf("%d",&n2);
    s2=(char*)malloc((n2+1)*sizeof(char));
   
    scanf("%s",s2);
    int a;
    a=makeEqual(s1,n1,s2,n2);
    printf("%d",a);
    return 0;
}