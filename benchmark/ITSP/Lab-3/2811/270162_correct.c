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
int main()
{
    float a1,b1,a2,b2,c1,c2;               //Declaration of the variables
    scanf("%f%f%f%f",&a1,&b1,&a2,&b2);     //For input by user
    if(a1/b1==a2/b2||a1==0&&a2==0||b1==0&&b2==0||a1==0&&b1==0||a2==0&&b2==0)                     //If lines are parallel/overlapping
    {
        printf("INF");
    }
    else                                    //If lines are not parallel
    {
        c1=((b2-b1)/(a1*b2-a2*b1));           //Computation of
        c2=((a2-a1)/(a2*b1-a1*b2));           //intersection point
        printf("(%.3f,%.3f)",c1,c2);        //Result
    }
	return 0;                               //The End
}