/*numPass=2, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:ACCEPTED, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Capital Letter"
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Capital Letter"
*/
#include<stdio.h>

int main()
{char C;
scanf("%c",&C);
  if ('A'<=C<='Z'){  
     printf("Capital Letter");
  } else if ('a'<=C<='z'){
     printf("Small Letter");
  }  
    
    return 0;
}