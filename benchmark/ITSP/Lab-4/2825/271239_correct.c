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

int main()
{
    float x,y,r,x1,y1,a,b,c;
    scanf("%f%f%f%f%f",&x,&y,&r,&x1,&y1);
    a=(((x1-x)*(x1-x))+((y1-y)*(y1-y)));
    b=r*r;
    c=a-b;
if (c<=0){
    if (c==0){
        printf("Point is on the Circle.");
    }
    else {
         printf("Point is inside the Circle.");
    }
}
else {
    printf("Point is outside the Circle.");
}
    return 0;
}