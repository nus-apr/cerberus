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

int main()
{
    float a,b,c,d,e,f;
    scanf("%f %f %f %f %f %f",&a,&b,&c,&d,&e,&f);//Taking the input
    if ((c-a)/(d-b)==(e-a)/(f-b)) { //Equating their slopes
       printf("All the points are on same line.");
    }
    else {
       printf("All the points are not on same line.");
    }
    return 0;
}