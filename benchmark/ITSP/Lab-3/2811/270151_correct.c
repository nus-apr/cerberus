/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"1 0 0 1", ExpOutput:"(1.000,1.000)
", Output:"(1.000,1.000)"
Verdict:ACCEPTED, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"INF"
Verdict:ACCEPTED, Visibility:1, Input:"-1.25 0 5 4", ExpOutput:"(-0.800,1.250)
", Output:"(-0.800,1.250)"
Verdict:ACCEPTED, Visibility:0, Input:"1 -2 -100 201", ExpOutput:"(203.000,101.000)
", Output:"(203.000,101.000)"
Verdict:ACCEPTED, Visibility:0, Input:"-1000 1 2000 -2", ExpOutput:"INF
", Output:"INF"
Verdict:ACCEPTED, Visibility:0, Input:"0 1 0.0000001 1", ExpOutput:"(-0.000,1.000)
", Output:"(-0.000,1.000)"
*/
#include<stdio.h>

int main(){
    float a1,b1,a2,b2; /*a1,b1,a2,b2 are variables of the given line */
    scanf("%f%f%f%f",&a1,&b1,&a2,&b2);/* values of a1,a2,b1,b2 are given by user */
    float X=(b2-b1)/((b2*a1-b1*a2));/* x-coordinate of intersection point*/
    float Y=(a2-a1)/((b1*a2)-(a1*b2));/*y-coordinate of intersection point*/
    if (a1*b2==b1*a2)        /*condition for no intersection*/
    {printf("INF");}/*if above boolean exp is true*/
    else
    {printf("(%.3f,%.3f)",X,Y);}/*if above boolean exp is false*/
	
	return 0;
}