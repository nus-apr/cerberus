/*numPass=2, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 5 7 2", ExpOutput:"The second largest number is 5", Output:"The second largest number is 1"
Verdict:ACCEPTED, Visibility:1, Input:"8 6 4 2", ExpOutput:"The second largest number is 6", Output:"The second largest number is 6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 10 15 3", ExpOutput:"The second largest number is 10", Output:"The second largest number is 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 3 3 2 ", ExpOutput:"The second largest number is 3", Output:"The second largest number is 1"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1 2", ExpOutput:"The second largest number is 1", Output:"The second largest number is 1"
*/
#include<stdio.h>

int main()
{   int a,b,c,d;
    scanf("%d %d %d %d",&a,&b,&c,&d);//input the numbers
    int g1=a,g2=c,s;
    if(b>a)
       {g1=b;
        b=a;
       }//g1 stores greatest and b stores lowest among a and b
    if(d>g2)
       {g2=d;
        d=c;
       }//g2 stores greatest and d stores lowest among c and d
    if((g1>g2)&&(b>g2))
       s=b;
    printf("The second largest number is %d",s);   
    return 0;
}