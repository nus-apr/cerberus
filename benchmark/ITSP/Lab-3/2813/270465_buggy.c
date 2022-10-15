/*numPass=2, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"(0.000,0.000)"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"(0.000,0.000)"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"(0.000,0.000)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"(0.000,0.000)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"(0.000,0.000)"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"INF"
*/
#include<stdio.h>

int main(){
	float a1,b1,a2,b2,c,d;
    scanf("%f,%f,%f,%f",&a1,&b1,&a2,&b2);
	c=(b1-b2)*(a1*a2)/((a2*b1)-(a1*b2));
	d=(a1-a2)*(b1*b2)/((a1*b2)-(a2*b1));
    if(a1*b2==b1*a2)
        printf("INF");
    else
        printf("(%.3f,%.3f)",c,d);
	return 0;
}