/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"Digit", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Digit", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"Digit", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:""
*/
#include<stdio.h>

int main()
{
    char ch='\0';
    scanf("%c",ch);
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