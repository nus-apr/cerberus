/*numPass=2, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(1.000,1.000)
", Output:"(-1.000,-1.000)"
Verdict:ACCEPTED, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"INF"
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1.25 0 5 4", ExpOutput:"(-0.800,1.250)
", Output:"(0.800,-1.250)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 -2 -100 201", ExpOutput:"(203.000,101.000)
", Output:"(-203.000,-101.000)"
Verdict:ACCEPTED, Visibility:0, Input:"-1000 1 2000 -2", ExpOutput:"INF
", Output:"INF"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1 0.0000001 1", ExpOutput:"(-0.000,1.000)
", Output:"(0.000,-1.000)"
*/
#include<stdio.h>
#include<float.h>
int main(){
	float a,b,c,d,m,x,y;
	scanf("%f%f%f%f",&a,&b,&c,&d);
	m = (c*b - a*d);
	if (m != 0) {
	    x = (d-b)/m;
	    y = (a-c)/m;
	    printf("(%.3f,%.3f)",x,y);
	} else {
	    printf("INF");
	} 
	    return 0;
}