/*numPass=3, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"H", ExpOutput:"Capital Letter", Output:"Digit"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:1, Input:"l", ExpOutput:"Small Letter", Output:"Digit"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"A", ExpOutput:"Capital Letter", Output:"Digit"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"Digit", Output:"Digit"
Verdict:WRONG_ANSWER, Visibility:0, Input:"z", ExpOutput:"Small Letter", Output:"Digit"
*/
#include<stdio.h>

int main(){
    char ch;//declaired character
    ch=0;
    scanf("%c",ch);//input ch
    if (ch>='A'&&ch<='Z'){//condition
        printf("Capital Letter");//output capital letter
    }else if (ch>='a'&&ch<='z'){//condition
        printf("Small Letter");//output small letter
    }else {
        printf("Digit");
    }
    
    return 0;
}