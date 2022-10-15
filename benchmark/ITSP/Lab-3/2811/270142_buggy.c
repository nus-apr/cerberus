/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(1.000,1.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1.25 0 5 4", ExpOutput:"(-0.800,1.250)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 -2 -100 201", ExpOutput:"(203.000,101.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1000 1 2000 -2", ExpOutput:"INF
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1 0.0000001 1", ExpOutput:"(-0.000,1.000)
", Output:""
*/
#include<stdio.h>

int main()
{
    float a,b,c,d,x,y; //variable declaration
    scanf("%f%f%f%f",a,b,c,d);
    x=(d-b)/(a*d-b*c);
    y=(a*d-b*c-d*c+b*c)/(a*d*d-b*c*d);
    if((a*d-b*c)==0 || (a*d*d-b*c*d)==0)
       printf("INF");
    else
    {
       printf("(%.3f,%.3f)",x,y);
    }
	return 0;
}