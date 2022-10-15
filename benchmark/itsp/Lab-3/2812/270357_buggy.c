/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:""
*/
#include<stdio.h>

int main()
{
    float a;
    scanf("%f,&a");
    if(a<0.0)
{	printf("%.4f is negative\n",a);}
	if(a==0.0)
{	printf("input is zero");}
	if(a>0.0)
{	printf("%.4f is positive\n",a);}
	return 0;
}