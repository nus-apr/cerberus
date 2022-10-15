/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 0 1", ExpOutput:"(1.000,1.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 0 1 0", ExpOutput:"INF
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1.25 0 5 4", ExpOutput:"(-0.800,1.250)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 -2 -100 201", ExpOutput:"(203.000,101.000)
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1000 1 2000 -2", ExpOutput:"INF
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"0 1 0.0000001 1", ExpOutput:"(-0.000,1.000)
", Output:""
*/
#include<stdio.h>

int main()
    {
	 float a1,b1,a2,b2;     //declaring variables.
	 float x,y;             //variables to store point of intersection.
	 scanf("%f%f%f%f",a1,b1,a2,b2);    //taking input.
	 if((-b2/a2)!=(-b1/a1)) //to check lines are not parallel.
	     {
	       x=(b2-b1)/((b2*a1)-(a2*b1)); //finding x-coordinate of point.
	       y=(a2-a1)/((b1*a2-b2*a1));   //finding y-coordinate of point.
	       printf("(%.3f,%.3f)",x,y);   //printing result.
	     }
 	 else                   //in case lines are parallel.
	      printf("INF");    //printing result.
	 return 0;
}