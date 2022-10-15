/*numPass=2, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"(0.000,-0.000)"
Verdict:ACCEPTED, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"INF"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"(-2.010,-102.010)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"(1.000,-0.000)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"(3.000,8.000)"
Verdict:ACCEPTED, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"INF"
*/
#include<stdio.h>

int main(){
    float a1,b1,a2,b2;
    scanf("%f %f %f %f",&a1,&b1,&a2,&b2);
    float x,y;
    
    if(a1*b2==b1*a2)
    {
        printf("INF");
    }
    else
    {
        y=((a1-a2)*(b1*b2))/((a1*b2)-(b1*a2));
        x=((b1-b2)*(a1*a2))/((a1*b2)-(a2*b1));
        printf("(%.3f,%.3f)",-x, -y);
    }
	
	return 0;
}