/*numPass=5, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000 is negative"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:""
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.0000 is positive"
Verdict:ACCEPTED, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000 is negative"
Verdict:ACCEPTED, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.0000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:""
*/
#include<stdio.h>

int main()
{
    float a;
    scanf("%f",&a);
    if(a>0)
    {
        printf("%.4f is positive",a);
    }
    else
    if(a<0)
    {
        printf("%.4f is negative",a);
    }
    else
    if(a=='0')
    {
      printf("input is zero");
    }
	return 0;
}