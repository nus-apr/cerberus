/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:""
*/
#include<stdio.h>

int main()
{
    int n,rev = 0;
    scanf("%d",&n);
    while(n>0) {
        rev = (rev*10);
        rev = rev + n%10;
        n = n/10;
    
    }
    return 0;
}