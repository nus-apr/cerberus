/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"0.0000"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.0000"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.0000"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000"
Verdict:WRONG_ANSWER, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.0000"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"0.0000"
*/
#include<stdio.h>

int main(){float a;
scanf("%f",&a);
printf("%.4f",a);	
	return 0;
}