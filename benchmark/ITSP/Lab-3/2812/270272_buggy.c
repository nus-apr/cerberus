/*numPass=2, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000 is negative-12.0000 is positive"
Verdict:ACCEPTED, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"input is zero"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:" is negative1.0000 is positive"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:" is negative0.0000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000 is negative-0.0000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:" is negative101.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"input is zero"
*/
#include<stdio.h>

int main(){
float a;
scanf("%f",&a);
if(a==0)
    printf("input is zero");
    else
    {
        if(a<0)
    printf("%.4f",a);
    printf(" is negative");
    
    printf("%.4f",a);
    printf(" is positive");
    }
	return 0;
}