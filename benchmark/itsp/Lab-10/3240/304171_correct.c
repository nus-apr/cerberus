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

int makeEqual(char * s1, int n1, char * s2, int n2)
{ int count=0;
   for(int i=0;i<n1;i++)
   { int flag=1;
       for(int j=0;j<n2;j++)
       {
           if(*(s1+i) == *(s2+j))
           {
               flag=0;
               *(s1+i) ='0'; *(s2+j) ='0';
               break;
           }
       }
       if(flag==1)
       {
           count++;
       }
   }
   for(int i=0;i<n2;i++)
   { int flag=1;
       for(int j=0;j<n1;j++)
       {
           if(*(s2+i) == *(s1+j))
           {
               flag=0;
               *(s2+i) ='0'; *(s1+j) = '0';
               break;
           }
       }
       if(flag==1)
       {
           count++;
       }
   }
   return count;
}

int main(){
    int n1;
    scanf("%d",&n1);
    char *s1;
    s1 = (char*)malloc(n1*sizeof(char));
    scanf("%s",s1);
    int n2;
    scanf("%d",&n2);
    char *s2;
    s2 = (char*)malloc(n2*sizeof(char));
    scanf("%s",s2);
   printf("%d",makeEqual(s1,n1,s2,n2));
    
    
    return 0;
}