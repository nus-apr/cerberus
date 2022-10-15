/*numPass=9, numTotal=9
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
Verdict:ACCEPTED, Visibility:0, Input:"ab", ExpOutput:"Good String", Output:"Good String"
*/
#include <stdio.h>
#include <stdlib.h>
int mod(int n)
{
    if(n<0)
        n=-n;
    return n;
}
int main()
{
    int n,i,j,count=0,a,b;
    char *s;
    scanf("%d",&n);
    s=(char*)malloc((n+1)*sizeof(char));
    scanf("%s",s);
    if(n>1)
    {
        for(i=1,j=n-1;i<n;i++,j--)
        {
            a=s[i]-s[i-1];
            b=s[j-1]-s[j];
            a=mod(a);
            b=mod(b);
            if(a==b)
                count++;
        }
        if(count==n-1)
            printf("Good String");
        else
            printf("Not Good String");
    }
    else if(n==0)
        printf("Good String");
    return 0;
}