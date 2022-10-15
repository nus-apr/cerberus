/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small Letter"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"Digit", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:""
*/
#include<stdio.h>

int main()
{
    char ch;
    scanf("%c",&ch);
    if('a'<ch && ch<'z'){
        printf("Small Letter");
    }
    else if('0'<ch && ch<'9'){
        printf("Digit");
    }
    else if('A'<ch && ch<'Z'){
        printf("Capital Letter");
    }
    return 0;
}