/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 5"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6"
Verdict:ACCEPTED, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 2"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1"
*/
#include<stdio.h>

int main()
{
    // Fill this area with your code.
    int a,b,c,d;
    
    scanf("%d %d %d %d",&a,&b,&c,&d);
    int max1=a;
    int max2=0;
    if(b>max1) {max1=b;}
    if(c>max1) {max1=c;}
    if(d>max1) {max1=d;}
    if(max1!=a)
    {
        max2=a;
        if((b>max2)&&(b!=max1))
        {
        max2=b;
        }
        if((c>max2)&&(c!=max1))
        {
        max2=c;
        }
        if((d>max2)&&(d!=max1))
        max2=d;
    }
    else
    {
        max2=b;
        if((c>max2)&&(c!=max1))
        {
            max2=c;
        }
        if((d>max2)&&(d!=max1))
        {
            max2=d;
            
        }
    }
    printf("The second largest number is %d",max2);
    return 0;
}