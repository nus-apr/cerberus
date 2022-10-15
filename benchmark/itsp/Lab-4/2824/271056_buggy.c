/*numPass=3, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"1004", ExpOutput:"Leap Year", Output:"Leap Year"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2009", ExpOutput:"Not Leap Year", Output:"Leap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2012", ExpOutput:"Leap Year", Output:"Leap Year"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2115", ExpOutput:"Not Leap Year", Output:"Leap Year"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1000", ExpOutput:"Not Leap Year", Output:"Leap Year"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1700", ExpOutput:"Not Leap Year", Output:"Leap Year"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1900", ExpOutput:"Not Leap Year", Output:"Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"2000", ExpOutput:"Leap Year", Output:"Leap Year"
*/
#include<stdio.h>

int main()
{
    // Fill this area with your code
    int y;    /*y is year which is given as input*/
    int a,b,c;
    a=y%4;
    b=y%100;
    c=y%400;
    
    if(a==0)
    {   if(b==0)
           {if(c==0)
            printf("Leap Year");
            else
            printf("Not Leap Year");
           }
        else
        printf("Leap Year");
    }
    else
    printf("Not Leap Year");
      
    
    return 0;
}