/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"12345", ExpOutput:"Reverse of 12345 is 54321", Output:"12345 Reverse of 1 is 54321"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1331", ExpOutput:"Reverse of 1331 is 1331", Output:"1331 Reverse of 1 is 1331"
Verdict:WRONG_ANSWER, Visibility:1, Input:"100", ExpOutput:"Reverse of 100 is 1", Output:"100 Reverse of 1 is 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"0", ExpOutput:"Reverse of 0 is 0", Output:"0 Reverse of 4798471 is 0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"Reverse of 10 is 1", Output:"10 Reverse of 1 is 1"
*/
#include<stdio.h>

int main()
{
  int a,b,c=0,e;
  scanf("%d",&a);
  printf("%d ",a);
  while(a){
      b=a%10;
      c=c*10+b;
      a=a/10;
  }
  printf("Reverse of %d is %d",e,c);
    return 0;
}