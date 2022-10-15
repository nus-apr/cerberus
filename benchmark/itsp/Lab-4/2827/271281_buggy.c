/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"1.0 0.0 2.0 0.0 3.0 0.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
Verdict:WRONG_ANSWER, Visibility:1, Input:"1.0 -2.0 5.2 3.0 0.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All points are not on the same line."
Verdict:WRONG_ANSWER, Visibility:1, Input:"1.0 -2.0 0.0 3.0 -6.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All points are not on the same line."
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0 0.0 1.0 1.0 2.0 2.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0 0.0 2.0 2.0 4.0 4.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0 0.0 2.0 3.0 4.0 5.0", ExpOutput:"All the points are not on same line.", Output:"All points are not on the same line."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0 -2.0 0.0 3.0 0.0 5.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
Verdict:WRONG_ANSWER, Visibility:0, Input:"0.0 -2.0 0.0 -3.0 0.0 -4.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
Verdict:WRONG_ANSWER, Visibility:0, Input:"5.0 -6.0 5.0 6.0 5.0 12.0", ExpOutput:"All the points are on same line.", Output:"All points are on the same line."
*/
#include<stdio.h>

int main()
{
    float x1,y1,x2,y2,x3,y3,m1,m2;
    scanf("%f %f %f %f %f %f",&x1,&y1,&x2,&y2,&x3,&y3);
    if(x2!=x1)
    {
        m1=(y2-y1)/(x2-x1);
    }
    if(x2!=x3)
    {
        m2=(y3-y2)/(x3-x2);
    }
    if((x1==x2)&&(x2==x3))
    {
        printf("All points are on the same line.");
    }
    else if(x1==x2&&x2!=x3)
    {
        printf("All points are not on the same line.");
    }
    else if(x1!=x2&&x2==x3)
    {
        printf("All points are not on the same line.");
    }
    else
    {
        if(m1==m2)
        {
           printf("All points are on the same line.");
        }
        else
        {
            printf("All points are not on the same line.");
        }
    }
    
    return 0;
}