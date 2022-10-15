/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:""
*/
#include<stdio.h>

int main()
{
	float a1,a2,b1,b2;
	scanf("%f %f %f %f",a1, a2, b1, b2);
	 /*float x= (1-(b1/b2))/((1/a2)-(b1/(a1*b2)));
	float y=b1*(1-(x/a1));
	if((a1/b1) == (a2/b2) )
	{
	    printf("INF");
	}*/
	printf("%f %f %f %f",a1+a2+b1+b2);
	return 0;
}