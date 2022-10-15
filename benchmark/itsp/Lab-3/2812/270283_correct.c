/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"-12", ExpOutput:"-12.0000 is negative", Output:"-12.0000 is negative"
Verdict:ACCEPTED, Visibility:1, Input:"0", ExpOutput:"input is zero", Output:"input is zero"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"1.0000 is positive", Output:"1.0000 is positive"
Verdict:ACCEPTED, Visibility:1, Input:"0.0000001", ExpOutput:"0.0000 is positive", Output:"0.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"-0.0000001", ExpOutput:"-0.0000 is negative", Output:"-0.0000 is negative"
Verdict:ACCEPTED, Visibility:0, Input:"101", ExpOutput:"101.0000 is positive", Output:"101.0000 is positive"
Verdict:ACCEPTED, Visibility:0, Input:"0000000", ExpOutput:"input is zero", Output:"input is zero"
*/
#include<stdio.h>

int main(){
    //to determine sign of a number
    float n;
    scanf("%f",&n);
    if(n>0)
    {
    printf("%.4f is positive",n);//number is positive
    }
    else{
        if (n==0)
        {
        printf("input is zero");//number is 0
        }
        else
        {
        printf("%.4f is negative",n);}}//number is negative
    
    
	
	return 0;
}