/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1.2 2.3 2.7 5.3 7.6", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
Verdict:ACCEPTED, Visibility:1, Input:"0.0 0.0 5.0 3.0 7.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
Verdict:ACCEPTED, Visibility:1, Input:"3.0 4.0 5.0 7.0 7.0", ExpOutput:"Point is on the Circle.", Output:"Point is on the Circle."
Verdict:ACCEPTED, Visibility:1, Input:"3.0 4.0 5.0 5.6 6.2", ExpOutput:"Point is inside the Circle.", Output:"Point is inside the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"-1.0 -2.0 5.0 1.5 2.0", ExpOutput:"Point is inside the Circle.", Output:"Point is inside the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 0.0 5.0 3.0 4.0", ExpOutput:"Point is on the Circle.", Output:"Point is on the Circle."
Verdict:ACCEPTED, Visibility:0, Input:"0.0 0.0 5.0 3.0 5.0", ExpOutput:"Point is outside the Circle.", Output:"Point is outside the Circle."
*/
#include<stdio.h>
#include<math.h>

int main()
{
    float x , y , x1 , y1 , r ,s ;
    // (x,y) are co-ordinates for center of circle .
    // (x1,y1) is point whose relative loacation w.r.t circle we have to see .
    // r is radius of circle .
    // s is distance of point from center of circle .
    scanf ("%f %f %f %f %f",&x,&y,&r,&x1,&y1);
    s = sqrtf(((x - x1)*(x - x1)) + ((y - y1)*(y - y1))) ;
    if (s>r){
        printf("Point is outside the Circle.");// if radius is less than distance from center , point is outside the circle .
    }
    else if (s==r){
        printf("Point is on the Circle.");// if radius is equal to distance from center , point is on the circumference .
    }
    else{
        printf("Point is inside the Circle.");
        
    }
    // if radius is greater than distance from center then point is inside the circle .
    
    
    return 0;
}