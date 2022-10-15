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

int main(){
	float a,b,s;
	 scanf("%f%f",&a,&b);
    s=(1.0/2.0)*(a*b);
    if (s<0)s=-1*(s);
	 printf("The area of (%.4f,%.4f), (%.4f,0) and (0,%.4f) is %.4f.",a,b,a,b,s);
	return 0;
}