/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"liril", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"oolaleloo", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"sorewaslerelsaweros", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"qwertyuiiuytrpwq", ExpOutput:"No
", Output:"No"
*/
#include <stdio.h>
#include <string.h>
int checkpal(char s[], int l, int a)
{
    int temp;
    if (a==l-a-1)
    {
        return 1;
    }
    if (l-a-1==1+a)
    {
        if(s[a]==s[l-a-1])
            return 1;
        else
            return 0;
    }
    if(s[a]==s[l-a-1])
    {
        a++;
        temp=checkpal(s,l,a);
        return temp;
    }
    else 
    return 0;
}
int main()
{
    char s[100];
    int l,ans,a=0;
    scanf("%s",s);
    l=strlen(s);
    ans=checkpal(s,l,a);
    if (ans==1)
        printf("Yes");
    else if(ans==0)
        printf("No");
    return 0;
}