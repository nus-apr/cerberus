/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small Letter"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small Letter"
*/
#include<stdio.h>

int main()
{
    char ch='\0';
    scanf("%c",&ch);
    if(ch>='A'&&ch<='Z')
    {
        printf("Capital Letter");
    }
    else if(ch>='a'&&ch<='z')
    {
        printf("Small Letter");
    }
    else if(ch>='0'&&ch<='9')
    {
        printf("Digit");
    }
    return 0;
}