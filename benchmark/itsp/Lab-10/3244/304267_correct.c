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
    if(n>0)
    return n;
    
    else return (-n);
}
void check(char*str,int n)
{
    int i;
    char*d;
     d=str+n-1;
    
    for( i=1;i<n-1;i++)
    {
        if(mod((int)*(str+i)-(int)*(str+i-1))!=mod((int)*(d-i)-(int)*(d+1-i)))
        {
            break;
        }
    }
    if(i==n-1||n==0)
    printf("Good String");
    else
    printf("Not Good String");
}

int main(){
    char*str;
    int n;
    str=(char*)malloc(n*sizeof(char));
    scanf("%d",&n);
    scanf("%s",str);
    check(str,n);
    return 0;
}