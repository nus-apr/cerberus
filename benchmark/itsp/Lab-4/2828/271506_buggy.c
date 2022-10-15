/*numPass=2, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Small Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Small Letter"
Verdict:ACCEPTED, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Small Letter"
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Small Letter"
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Small Letter"
Verdict:ACCEPTED, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small Letter"
*/
#include<stdio.h>

int main()
{
    char x;
    scanf ("%c",&x);
    if('x'>=65 && 'x'<=90)
   { printf("Capital Letter");}
   else if ('x'>=48 && 'x'<=57)
   { printf ("Digit");}
   else if ('x'>=97 && 'x'<=122)
   { printf ("Small Letter");}

    
    return 0;
}