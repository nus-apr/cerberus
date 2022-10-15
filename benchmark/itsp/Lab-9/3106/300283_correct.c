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
void check_palindrome(char s[],int x,int y,char*z) 
{
    if(x==y/2) printf("Yes"); 
    else 
    {
        if(*s==*(z+x-1)) check_palindrome(s+1,x-1,y,z);
        else printf("No");
    }
}
int main()
{
    char s[100];
    scanf("%s",s);
    int x=strlen(s);
    char*y;
    y=s;
    check_palindrome(s,x,x,y);
    return 0;
}