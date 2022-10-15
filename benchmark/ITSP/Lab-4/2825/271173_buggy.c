/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1.2 2.3 2.7 5.3 7.6", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Cicle."
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0 0.0 5.0 3.0 7.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Cicle."
Verdict:ACCEPTED, Visibility:1, Input:"3.0 4.0 5.0 7.0 7.0", ExpOutput:"Point is on the Circle.", Output:"Point is on the Circle."
Verdict:ACCEPTED, Visibility:1, Input:"3.0 4.0 5.0 5.6 6.2", ExpOutput:"Point is inside the Circle.", Output:"Point is inside the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"-1.0 -2.0 5.0 1.5 2.0", ExpOutput:"Point is inside the Circle.", Output:"Point is inside the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 0.0 5.0 3.0 4.0", ExpOutput:"Point is on the Circle.", Output:"Point is on the Circle."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0 0.0 5.0 3.0 5.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Cicle."
*/
#include<stdio.h>
#include<math.h>

int main()
{
    float x,y,r,x1,y1;
    scanf("%f %f %f %f %f",&x,&y,&r,&x1,&y1);//input x,y,r,x1,y1
    
    float d=sqrtf((x1-x)*(x1-x)+(y1-y)*(y1-y));
    //compute distance between point and centre of circle
    
    if ((d==r)||(d<r)) {
        if (d==r) printf("Point is on the Circle.");
        else printf("Point is inside the Circle.");
    } else {
        printf("Point is outside the Cicle.");
    }    
    
    return 0;
}