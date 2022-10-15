/*numPass=5, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"capital Letter"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Small Letter"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Digit"
Verdict:ACCEPTED, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Small Letter"
*/
#include<stdio.h>

int main()
{
    char ch;               //declaration of the character to be input
    scanf("%c",&ch);
    if(ch>='a'&& ch<='z')  //Test for small letter
    {
        printf("Small Letter");
    }
    else if(ch>='A'&& ch<='Z')  //Test for capital letter
         {
            printf("capital Letter");
         }    
            else if(ch>='0' && ch<='9')  //Test for digit
                 {
                     printf("Digit");
                 }
    
    return 0;
}