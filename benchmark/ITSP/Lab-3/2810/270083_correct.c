/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"1 1", ExpOutput:"The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000."
Verdict:ACCEPTED, Visibility:1, Input:"-1 1", ExpOutput:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is 0.5000."
Verdict:ACCEPTED, Visibility:0, Input:"-100 -9", ExpOutput:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is 450.0000.
", Output:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is 450.0000."
Verdict:ACCEPTED, Visibility:0, Input:"0.0001 -1000", ExpOutput:"The area of (0.0001,-1000.0000), (0.0001,0) and (0,-1000.0000) is 0.0500.
", Output:"The area of (0.0001,-1000.0000), (0.0001,0) and (0,-1000.0000) is 0.0500."
*/
#include<stdio.h>
#include<math.h>

int main(){
	float a,b,area;
	scanf("%f%f",&a,&b);
	area=(0.5*a*b);
	printf("The area of (%6.4f,%6.4f), (%6.4f,0) and (0,%6.4f) is %6.4f.",a,b,a,b,fabs(area));
	return 0;
}