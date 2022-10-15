/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000 -12.000000 is negative"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"0.0000input is zero"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.00001.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.00000.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000 -0.000000 is negative"
Verdict:WRONG_ANSWER, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.0000101.000000 is positive"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"0.0000input is zero"
*/
#include<stdio.h>

int main(){
    float n ;         /* variable declaration*/
    
        

            scanf("%f",&n);
        printf("%.4f",n);
     
    if(n<0)
        {printf(" %f is negative",n);}
    
    else if(n>0)
    {printf("%f is positive",n);}
    
    else
    {printf("input is zero");}
    
}