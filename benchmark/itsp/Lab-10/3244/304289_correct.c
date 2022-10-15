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
int checkstr(char* S,char* R,int n)
{
    int flag=0,i;
    for(i=1;i<n;i++)
    {
        flag=0;
        if((*(S+i))-(*(S+(i-1)))==(*(R+i))-(*(R+(i-1)))||(*(S+i))-(*(S+(i-1)))==-((*(R+i))-(*(R+(i-1)))))//given condition for good string
        flag++;
        else 
        return 0;//if condition is not followed no need to check further
    }
    //in case condition is true for all elements of S and R
    return 1;
}

int main()
{
    char *S,*R;
    int n,i,ans;
    scanf("%d",&n);
    S=(char*)calloc(n,sizeof(char));//memory allocation dynamically
    R=(char*)calloc(n,sizeof(char));//memory allocation dynamically
    scanf("%s",S);
    for(i=0;i<n;i++)
    {
        *(R+i)=*(S+(n-1-i));
    }
    ans=checkstr(S,R,n);//function calling
    if(ans==1)
    printf("Good String");
    if(ans==0)
    printf("Not Good String");
    return 0;
}