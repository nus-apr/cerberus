/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
abcde", ExpOutput:"Good String", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"8
pqrsabcd", ExpOutput:"Good String", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
azpg", ExpOutput:"Not Good String", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam", ExpOutput:"Not Good String", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
aaaazzzz", ExpOutput:"Good String", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
abczpq", ExpOutput:"Not Good String", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
abcpqz", ExpOutput:"Not Good String", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
acegikmo", ExpOutput:"Good String", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"1"
*/
#include <stdio.h>
#include <stdlib.h>

int mod(int a,int b)
{   int z=a-b;
if(z>0) return z;
else return -z;
}

int main(){int n,i,good=1;
   char *str1,*str2;
   scanf("%d",&n);
   str1=(char*)malloc(n*sizeof(char));
   scanf("%s",str1);
   str2=(char*)malloc(n*sizeof(char));
   
   for(i=0;i<n;i++)
   str2[i]=str1[n-i-1];
   
   for(i=1;i<n;i++)
   {if(mod(str1[i],str1[i-1])!=mod(str2[i],str2[i-1]))
   {
       good=0;
       break;
   }}
   printf("%d",good);
       
       
       
   
   
   
   
   
   
   
   
   
   
   
   
    return 0;
}