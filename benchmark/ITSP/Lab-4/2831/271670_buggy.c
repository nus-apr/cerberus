/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"54321"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"1331"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"1"
*/
#include<stdio.h>

int main()
{
    // Fill this area with your code.
    int num,revnum=0;
    scanf("%d",&num);
    
    do
    {
        revnum=revnum*10;
        revnum=revnum+num%10;
        num=num/10;
        
    }while(num!=0);
    printf("%d",revnum);
    return 0;
}