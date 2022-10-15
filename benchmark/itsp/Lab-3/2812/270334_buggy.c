/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.000000 is negative"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"0.000000 is zero"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.000000 is negative"
Verdict:WRONG_ANSWER, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"0.000000 is zero"
*/
#include<stdio.h>
#include<math.h>

int main(){
    float a;
    float b=0;
    scanf("%f",&a);
    if (a<b){
        printf("%f is negative",a);
    }
    if (a>b){
        printf("%f is positive",a);
    }
    if (a==b){
        printf("%f is zero",a);
    }
	
	return 0;
}