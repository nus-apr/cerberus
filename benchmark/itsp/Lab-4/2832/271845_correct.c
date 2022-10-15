/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Obtuse Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
*/
#include<stdio.h>

int main()
{
    int a,b,c;              //declaring variables for sides of triangle
    scanf("%d",&a);        
    scanf("%d",&b);         //inputting sides 
    scanf("%d",&c);
    if(((a+b)<=c)||((b+c)<=a)||((a+c)<=b)) //checking for invalid
    printf("Invalid Triangle");            //triangle
    else
    if(((c*c)==(a*a+b*b))||((b*b)==(a*a+c*c))||((a*a)==(b*b+c*c)))
    printf("Right Triangle");                 //for right triangle
    else
    if(((c*c)>(a*a+b*b))||((b*b)>(a*a+c*c))||((a*a)>(b*b+c*c)))
    printf("Obtuse Triangle");                //for obtuse triangle
    else
    printf("Acute Triangle");                 //for acute triangle
    return 0;
}