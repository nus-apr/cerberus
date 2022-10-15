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
    int i,j,k,count,l;
    count=0;
    for(i=0;i<n1;i++)
    {
        for(j=0;j<n2;j++)
        {
            if(s1[i]==s2[j])
            {
               s1[i]='#';
               s2[j]='#';
                break;
            }    
        }
    }
    for(k=0;k<n1;k++)
    {
        if(s1[k]=='#')
        count++;
    }
    for(l=0;l<n2;l++)
    {
        if(s2[l]=='#')
        count++;
    }
    return(n1+n2-count);


}

int main(){
    char*a;
    char*b;
    int n1,n2;
    scanf("%d",&n1);
    a=(char*)malloc(n1*sizeof(char));
    scanf("%s",a);
    scanf("%d",&n2);
    b=(char*)malloc(n2*sizeof(char));
    scanf("%s",b);
    printf("%d",makeEqual(a,n1,b,n2));



    return 0;
}