/*numPass=6, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"1004", ExpOutput:"Leap Year", Output:"Not Leap YearLeap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2009", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2012", ExpOutput:"Leap Year", Output:"Not Leap YearLeap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2115", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1000", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1700", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1900", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"2000", ExpOutput:"Leap Year", Output:"Leap Year"
*/
#include<stdio.h>

int main()
{
    int Y;
    scanf("%d",&Y); 
    if(Y%4==0) // % used for divisiblity
    {
     if(Y%100==0&&Y%400==0)
     printf("Leap Year");
     else
     printf("Not Leap Year");
     if(Y%100!=0)
     printf("Leap Year");
    }
    else
        printf("Not Leap Year");
    // Fill this area with your code.
    return 0;
}