/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
*/
#include<stdio.h>

int main()
{
    int a,b,c;
    scanf("%d %d %d",&a,&b,&c); //  Scan the sides of triangle
    
    if(a+b>c && b+c >a && a+c>b) 
    {if(a*a+b*b-c*c==0 || b*b+c*c-a*a==0 || a*a+c*c-b*b==0)      
      {printf("Right Triangle");} 
     else if(a*a+b*b -c*c> 0 && b*b+c*c-a*a >0 && a*a+c*c-b*b>0)
     {printf("Acute Triangle");} 
     else if(a*a+b*b-c*c <0 && b*b+c*c<a*a && a*a+c*c<b*b)
     {printf("Obtuse Triangle");}
    }
    else
    {printf("Invalid Triangle");}
    
    return 0;}
    