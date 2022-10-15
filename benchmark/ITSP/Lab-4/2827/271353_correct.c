/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"1.0 0.0 2.0 0.0 3.0 0.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
Verdict:ACCEPTED, Visibility:1, Input:"1.0 -2.0 5.2 3.0 0.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All the points are not on same line."
Verdict:ACCEPTED, Visibility:1, Input:"1.0 -2.0 0.0 3.0 -6.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All the points are not on same line."
Verdict:ACCEPTED, Visibility:1, Input:"0.0 0.0 1.0 1.0 2.0 2.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
Verdict:ACCEPTED, Visibility:1, Input:"0.0 0.0 2.0 2.0 4.0 4.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
Verdict:ACCEPTED, Visibility:1, Input:"0.0 0.0 2.0 3.0 4.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All the points are not on same line."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 -2.0 0.0 3.0 0.0 5.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 -2.0 0.0 -3.0 0.0 -4.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
Verdict:ACCEPTED, Visibility:0, Input:"5.0 -6.0 5.0 6.0 5.0 12.0", ExpOutput:"All the points are on same line.", Output:"All the points are on same line."
*/
#include<stdio.h>
#include<stdlib.h>

int main()
{  float x1,y1,x2,y2,x3,y3;
   scanf("%f %f %f %f %f %f",&x1,&y1,&x2,&y2,&x3,&y3);/*co-ordinates of points*/
   if ((y3-y2)/(x3-x2)==(y2-y1)/(x2-x1)){
    printf("All the points are on same line.");   
   }else{
   printf("All the points are not on same line.");       
   }
    return 0;
}