/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"4", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"20", Output:"20"
Verdict:ACCEPTED, Visibility:1, Input:"10", ExpOutput:"220", Output:"220"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"10", Output:"10"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"1", Output:"1"
Verdict:ACCEPTED, Visibility:0, Input:"20", ExpOutput:"1540", Output:"1540"
*/
#include<stdio.h>

int main(){
    int i=1,n,sum=0,x;
    for(;n>=0,i<=n;i++)
    {scanf("%d",&n);
    x=i*(n-i+1);
      sum = sum + x;}
      printf("%d",sum);
	//Enter your code here
	return 0;
}