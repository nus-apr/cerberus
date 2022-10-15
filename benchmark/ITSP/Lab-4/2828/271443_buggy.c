/*numPass=5, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small letter"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small letter"
*/
#include<stdio.h>

int main()
{
    char x;   
    scanf("%c",&x);
    if ((x>='A')&&(x<='Z'))
       printf("Capital Letter");
    else 
       if((x>='a')&&(x<='z'))
       printf("Small letter");
    else 
       if((x>=48)&&(x<=57))      
       printf("Digit");
    return 0;
}