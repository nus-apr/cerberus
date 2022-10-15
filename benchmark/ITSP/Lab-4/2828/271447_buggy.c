/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small Letter"
*/
#include<stdio.h>

int main()
{
    char d;
    scanf("%c",&d);
    if('a'<=d && d<='z'){
    printf("Small Letter");
    } else{
    if('A'<=d && d<='Z');
    printf("Capital Letter");
    }
    
    // Fill this area with your code.
    return 0;
}