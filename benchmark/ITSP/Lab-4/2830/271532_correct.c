/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 5"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6"
Verdict:ACCEPTED, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 10"
Verdict:ACCEPTED, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 3"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1"
*/
#include<stdio.h>

int main()
{
    // Fill this area with your code.
    int a,b,c,d;
    scanf ("%d%d%d%d",&a,&b,&c,&d);
    if (a>=b&&a>=c&&a>=d)
    {
        if (b>=c&&b>=d)
        {
            printf("The second largest number is %d",b);
        }
        else
        {
            if (c>=d)
            {
                printf("The second largest number is %d",c);
            }
            else
            {
                printf("The second largest number is %d",d);
            }
        }
    }
    
     else if (b>=a&&b>=c&&b>=d)
    {
        if (a>=c&&a>=d)
        {
            printf("The second largest number is %d",a);
        }
        else
        {
            if (c>=d)
            {
                printf("The second largest number is %d",c);
            }
            else
            {
                printf("The second largest number is %d",d);
            }
        }
    }
    
     else if (c>=b&&c>=a&&c>=d)
    {
        if (a>=b&&a>=d)
        {
            printf("The second largest number is %d",a);
        }
        else
        {
            if (b>=d)
            {
                printf("The second largest number is %d",b);
            }
            else
            {
                printf("The second largest number is %d",d);
            }
        }
    }
    
     else if (d>=b&&d>=c&&d>=a)
    {
        if (b>=c&&b>=a)
        {
            printf("The second largest number is %d",b);
        }
        else
        {
            if (c>=a)
            {
                printf("The second largest number is %d",c);
            }
            else
            {
                printf("The second largest number is %d",a);
            }
        }
    }
    
    return 0;
}