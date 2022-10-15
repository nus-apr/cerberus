/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000 is negative"
Verdict:ACCEPTED, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"input is zero"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.0000 is positive"
Verdict:ACCEPTED, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000 is negative"
Verdict:ACCEPTED, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"input is zero"
*/
#include<stdio.h>
#include<math.h>

int main(){
    float a;
    float b=0;/*b is defined to compare input with 0*/
    scanf("%f",&a);
    if (a<b){
        printf("%.4f is negative",a);
    }
    if (a>b){
        printf("%.4f is positive",a);
    }
    if (a==b){
        printf("input is zero");
    }
	
	return 0;
}