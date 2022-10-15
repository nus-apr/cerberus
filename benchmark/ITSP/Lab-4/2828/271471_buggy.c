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
{   char ch;
    scanf("%c",ch);
    if(  97<=ch && ch<=122)
    printf("Small Letter");
    if(65<=ch && ch<=90)
    printf("Capital Letter");
    if(48<=ch && ch<=57)
    printf("Digit");// Fill this area with your code.
    return 0;
}