/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 1", ExpOutput:"The area of (1.0000,1.0000), (1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of ( 1.0000,1.0000), ( 1.0000,0) and (0,1.0000) is  0.5000."
Verdict:WRONG_ANSWER, Visibility:1, Input:"-1 1", ExpOutput:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is 0.5000.
", Output:"The area of (-1.0000,1.0000), (-1.0000,0) and (0,1.0000) is  0.5000."
Verdict:WRONG_ANSWER, Visibility:0, Input:"-100 -9", ExpOutput:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is 450.0000.
", Output:"The area of (-100.0000,-9.0000), (-100.0000,0) and (0,-9.0000) is  450.0000."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0001 -1000", ExpOutput:"The area of (0.0001,-1000.0000), (0.0001,0) and (0,-1000.0000) is 0.0500.
", Output:"The area of ( 0.0001,-1000.0000), ( 0.0001,0) and (0,-1000.0000) is  0.0500."
*/
#include<stdio.h>
#include<math.h>                   //to use fabs function.

int main()
    {
      float a,b,area;              //declaring variables to take input.
      scanf("%f%f",&a,&b);         //values being enterred.
      area=fabs(0.5*a*b);          //area of right angled triangle=0.5*base                                  *height.
      printf("The area of (% .4f,%.4f), (% .4f,0) and (0,%.4f) is %                  .4f.",a,b,a,b,area);   //printing the output.
      return 0; 
    }