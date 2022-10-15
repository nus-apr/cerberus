/*numPass=3, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital letter"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small letter"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Capital letter"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small letter"
*/
#include<stdio.h>

int main()
{
     char ch;
     //the character that has to be entered..
     scanf("%c",&ch);
     //input from user
     if(ch>='a'&&ch<='z') printf("Small letter");
     //if the character is between a to z
     if(ch>='A'&&ch<='Z') printf("Capital letter");
     //if the charater is between A to Z
     if(ch>='0'&&ch<='9') printf("Digit");
     //if the character is between 0 to 9
    return 0;
}