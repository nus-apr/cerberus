/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:""
*/
#include <stdio.h>
#include <stdlib.h>

int makeEqual(char * s1, int n1, char * s2, int n2){
    int i;
    for(i=0;i<n1;i++)
    {
        
    }


}

int main(){
    char*a;
    char*b;
    int n1,n2,i,j;
    scanf("%d",&n1);
    a=(char*)malloc(n1*sizeof(char));
    scanf("%s",a);
    scanf("%d",&n2);
    b=(char*)malloc(n2*sizeof(char));
    scanf("%s",b);
    



    return 0;
}