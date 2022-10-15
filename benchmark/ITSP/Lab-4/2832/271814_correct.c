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
    int a,b,c; // a,b,c represent three sides of a triangle
    scanf ("%d",&a);
    scanf ("%d",&b);
    scanf ("%d",&c);
    
    if (a+b<=c||b+c<=a||c+a<=b)
    
    printf ("Invalid Triangle");
    
    else
    {if (c>=a && c>=b)
    if ((((a*a)+(b*b))>c*c)&& ((a+b)>c))
    printf ("Acute Triangle");
    else if ((((a*a)+(b*b))<c*c)&& ((a+b)>c))
    printf ("Obtuse Triangle");
    else if ((((a*a)+(b*b))==c*c)&& ((a+b)>c))
    printf ("Right Triangle");
    
    if (a>=b && a>=c)
    
    if ((((c*c)+(b*b))>a*a)&& ((a+b)>c))
    printf ("Acute Triangle");
    else if ((((c*c)+(b*b))<a*a)&& ((a+b)>c))
    printf ("Obtuse Triangle");
    else if ((((c*c)+(b*b))==a*a)&& ((a+b)>c))
    printf ("Right Triangle");
    
    if (b>=a && b>=c)
    
    if ((((a*a)+(c*c))>b*b)&& ((a+b)>c))
    printf ("Acute Triangle");
    else if ((((a*a)+(c*c))<b*b)&& ((a+b)>c))
    printf ("Obtuse Triangle");
    else if ((((a*a)+(c*c))==b*b)&& ((a+b)>c))
    printf ("Right Triangle");}
    
    return 0;
}