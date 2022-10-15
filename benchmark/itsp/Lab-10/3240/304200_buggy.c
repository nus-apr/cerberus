/*numPass=1, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"2461"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"2462"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"247"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"24686"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"24681012140"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"24681012142"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"16"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"2468106"
*/
#include <stdio.h>
#include <stdlib.h>

int makeEqual(char * s1, int n1, char * s2, int n2){
//s1 = (char*)malloc((n1)*sizeof(char));
//s2 = (char*)malloc((n2)*sizeof(char));
int i,j;
int x=0;
for(i=0;i<n1;i++){
    for(j=0;j<n2;j++){
        if(*(s1+i)==*(s2+j)){
            x = x+2;
            printf("%d",x);
            *(s2+j)='\0';
            break;
        }
    }
   
}
 return n1+n2-x;
    
}

int main(){
int n1,n2;
scanf("%d",&n1);
char *s1,*s2;
s1 = (char*)malloc((n1)*sizeof(char));
s2 = (char*)malloc((n2)*sizeof(char));
scanf("%s",s1);
scanf("%d",&n2);
scanf("%s",s2);
int count = makeEqual(s1,n1,s2,n2);
printf("%d",count);





    return 0;
}