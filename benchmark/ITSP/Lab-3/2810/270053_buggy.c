/*numPass=3, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"1 1", ExpOutput:"The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000."
Verdict:ACCEPTED, Visibility:1, Input:"-1 1", ExpOutput:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is 0.5000."
Verdict:ACCEPTED, Visibility:0, Input:"-100 -9", ExpOutput:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is 450.0000.
", Output:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is 450.0000."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0001 -1000", ExpOutput:"The area of (0.0001,-1000.0000), (0.0001,0) and (0,-1000.0000) is 0.0500.
", Output:"The area of (0.0001,-1000.0000), (0.0001,0) and (0,-1000.0000) is 0.0000."
*/
#include<stdio.h>
#include<stdlib.h>
int main(){
    float a,b,area;         //initialising the variables
    scanf("%f %f",&a,&b);   //accepting values from user
    area=0.5*abs(a)*abs(b);           //evaluating area
    printf("The area of (%.4f,%.4f), (%.4f,0) and (0,%.4f) is %.4f.",a,b,a,b,area);                             //printing
	return 0;                               
}