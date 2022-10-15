/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"1004", ExpOutput:"Leap Year", Output:"Leap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2009", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2012", ExpOutput:"Leap Year", Output:"Leap Year"
Verdict:ACCEPTED, Visibility:1, Input:"2115", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1000", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1700", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"1900", ExpOutput:"Not Leap Year", Output:"Not Leap Year"
Verdict:ACCEPTED, Visibility:0, Input:"2000", ExpOutput:"Leap Year", Output:"Leap Year"
*/
#include<stdio.h>

int main()
{
    int a;
    scanf("%d",&a);
    if (a%4==0){
        if (a%100==0){
            if (a%400==0){
                printf("Leap Year");
            }else{
                printf("Not Leap Year");
            }
        }else{
            printf("Leap Year");
        }
        
    }else{
        printf("Not Leap Year");
    }    
    return 0;
}