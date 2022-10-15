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
 int i=0;
 int palin(char str[], int i, int n)
 {
     n=strlen(str);
     if(i==n/2){
        printf("Yes");
        return 0;
     }
     if(str[i]==str[n-1-i]) palin(str, i+1, n); 
     else 
     {
         printf("No");
         return 0;
     }
 }
int main()
{
    char str[100];
    scanf("%s ", str);
    palin(str, 0, strlen(str));
    return 0;
}