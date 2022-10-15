/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"5
abcde", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"8
pqrsabcd", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:1, Input:"4
azpg", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:1, Input:"7
labexam", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
aaaazzzz", ExpOutput:"Good String", Output:"Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abczpq", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"6
abcpqz", ExpOutput:"Not Good String", Output:"Not Good String"
Verdict:ACCEPTED, Visibility:0, Input:"8
acegikmo", ExpOutput:"Good String", Output:"Good String"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Good StringNot Good String"
*/
#include <stdio.h>
#include <stdlib.h>
int mod_of_diff(int a,int b)
{
   if(a-b<0)
   return (b-a);
   else
   return a-b;
}
int main(){
    int n,a[20],b[20],i,count=0;
    char *s1,*s2;
    scanf("%d",&n);
    if(n==0)
    printf("Good String");
    s1=(char *)malloc((n+1)*sizeof(char));
    s2=(char *)malloc((n+1)*sizeof(char));
    scanf("\n%s",s1);
    for(i=0;i<n;i++)
    {
        *(s2+i)=*(s1+n-1-i);
    }
    for(i=0;i<n-1;i++)
    {
        a[i]=mod_of_diff(*(s1+i+1),*(s1+i));
    }
    for(i=0;i<n-1;i++)
    {
        b[i]=mod_of_diff(*(s2+i+1),*(s2+i));
    }
    for(i=0;i<n-1;i++)
    {
       if(a[i]==b[i])
       count++;
    }
    if(count==n-1)
    printf("Good String");
    else
    printf("Not Good String");
    return 0;
}