/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"Reverse of 12345 is 54321"
Verdict:ACCEPTED, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"Reverse of 1331 is 1331"
Verdict:ACCEPTED, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"Reverse of 100 is 1"
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"Reverse of 0 is 0"
Verdict:ACCEPTED, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"Reverse of 10 is 1"
*/
#include<stdio.h>

int main()
{
    int a, r, x;
    int i= 0;
    scanf("%d", &a);
    x=a;
    while(a>0){
        r= a%10;
        i= (i*10)+ r;
        a= a/10;
    }
    printf("Reverse of %d is %d", x, i);
    return 0;
}