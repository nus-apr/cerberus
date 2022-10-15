/*numPass=4, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"1 0 0 1", ExpOutput:"(0.000,0.000)
", Output:"(0.000,0.000)"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:"(-nan,-nan)"
Verdict:ACCEPTED, Visibility:1, Input:"100 100 -1 -101", ExpOutput:"(-2.010,102.010)
", Output:"(-2.010,102.010)"
Verdict:ACCEPTED, Visibility:0, Input:"1000 000 1 -1", ExpOutput:"(1.000,0.000)
", Output:"(1.000,0.000)"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -2 -3 -4", ExpOutput:"(3.000,-8.000)
", Output:"(3.000,-8.000)"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 0 000 0000", ExpOutput:"INF
", Output:"(-nan,-nan)"
*/
#include<stdio.h>

int main(){
    float x,y;   
    /*represent x and y coordinates of intersection point*/
    float a1,b1,a2,b2; 
    scanf("%f%f%f%f",&a1,&b1,&a2,&b2);
    if((a2/a1)==(b2/b1)||(a1/a2)==(b1/b2)) 
    /*in case lines are parallel then there is no intersection point*/
    {
    printf("INF");    
    }
    else 
    /*gives intersection point of the form(x,y)*/
    {
     x=((a1*a2)*(b1-b2))/(b1*a2-b2*a1);
     y=((b1*b2)*(a1-a2))/(a1*b2-a2*b1);
     printf("(%.3f,%.3f)",x,y);
    }
	
	return 0;
}