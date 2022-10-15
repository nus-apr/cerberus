/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"5"
Verdict:WRONG_ANSWER, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"3"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"1"
*/
#include<stdio.h>

int main()
{
    // Fill this area with your code.
    int a,b,c,d;
    int large1,large2,large3;
    scanf("%d",&a);
    scanf("%d",&b);
    if(a>b)
    {
        large1=a;
        large2=b;
    }
    else
    {
        large1=b;
        large2=a;
    }
    scanf("%d",&c);
    if(c>large2)
    {
        if(c>large1)
        {
            large3=large2;
            large2=large1;
            large1=c;
        }
        else
        {
            large3=large2;
            large2=c;
        }
    }
    else
    {
        large3=c;
    }
    scanf("%d",&d);
    if(d>large2)
    {
        if(d>large1)
        {
            large2=large1;
        }
        else
        {
            large2=d;
        }
    }
    printf("%d",large2);
    
    return 0;
}