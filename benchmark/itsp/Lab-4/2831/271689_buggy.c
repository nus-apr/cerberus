/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"Revrse of 12345 is 54321"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"Revrse of 1331 is 1331"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"Revrse of 100 is 001"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"Revrse of 0 is "
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"Revrse of 10 is 01"
*/
#include<stdio.h>

int main()
{
    int a;
    scanf("%d",&a);
    printf("Revrse of %d is ",a);
    for(int i=a;i!=0;i=i/10)
    {
        int rem=i%10;
        printf("%d",rem);
    }
        
    return 0;
}