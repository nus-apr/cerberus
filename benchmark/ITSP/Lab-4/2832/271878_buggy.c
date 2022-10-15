/*numPass=4, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"Right Triangle", Output:"Right Triangle"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 3", ExpOutput:"Acute Triangle", Output:"Acute Triangle"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3 7", ExpOutput:"Invalid Triangle", Output:"Acute Triangle"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3 5", ExpOutput:"Obtuse Triangle", Output:"Acute Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"1 2 3", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:ACCEPTED, Visibility:0, Input:"3 6 2", ExpOutput:"Invalid Triangle", Output:"Invalid Triangle"
Verdict:WRONG_ANSWER, Visibility:0, Input:"12 13 5", ExpOutput:"Right Triangle", Output:"Invalid Triangle"
*/
#include<stdio.h>

int main()
{
    int a,b,c;
    scanf("%d %d %d",&a,&b,&c);
    int max,min,mid;
    if((a>b)&&(a>c))
        max=a;
    if((c>b)&&(c>a))
        max=c;
     if((b>c)&&(b>a))
        max=b;
    if((a<b)&&(a<c))
        min=a;
    if((c<b)&&(c<a))
        min=c;
     if((b<c)&&(b<a))
        min=b;
    if((a!=min)&&(a!=max))
        mid=a;
    if((b!=min)&&(b!=max))
        mid=b;
    else
        mid=c;    
    if((min+mid)>(max))    
        {
            int cos=(min*min)+(mid*mid)-(max*max);
            if(cos==0)
                printf("Right Triangle");
            if(cos>0)
                printf("Acute Triangle");
            if(cos<0)
                printf("Obtuse Triangle");
        }
    else
        printf("Invalid Triangle");

            
            
        
        
        
        
    return 0;
}