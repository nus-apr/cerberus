/*numPass=3, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1.2 2.3 2.7 5.3 7.6", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
Verdict:ACCEPTED, Visibility:1, Input:"0.0 0.0 5.0 3.0 7.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
Verdict:WRONG_ANSWER, Visibility:1, Input:"3.0 4.0 5.0 7.0 7.0", ExpOutput:"Point is on the Circle.", Output:"Point is outside the Circle."
Verdict:WRONG_ANSWER, Visibility:1, Input:"3.0 4.0 5.0 5.6 6.2", ExpOutput:"Point is inside the Circle.", Output:"Point is outside the Circle."
Verdict:WRONG_ANSWER, Visibility:0, Input:"-1.0 -2.0 5.0 1.5 2.0", ExpOutput:"Point is inside the Circle.", Output:"Point is outside the Circle."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0 0.0 5.0 3.0 4.0", ExpOutput:"Point is on the Circle.", Output:"Point is outside the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 0.0 5.0 3.0 5.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
*/
#include<stdio.h>

int main()
{
 float x,y;//cordinate of the center of the circle
 float r;// radius of the circle
 float x1,y1;// the another cordinate provided by user
 scanf("%f%f%f%f%f",&x,&y,&r,&x1,&y1);
 float a=(x1-x)*(x1-x);
 float b=(y1-y)*(y1-y);
 float c=a+b;//distance between origen and cordinates providade by user
 float d=sqrtf(c);
 if(c<r)
 printf("Point is inside the Circle.");
 else if(c==r)
     printf("Point is on the Circle.");
else
    printf("Point is outside the Circle.");
    return 0;
}
