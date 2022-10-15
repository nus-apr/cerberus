/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"4", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"20", Output:"10"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10", ExpOutput:"220", Output:"165"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"10", Output:"4"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"1", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20", ExpOutput:"1540", Output:"1330"
*/
#include<stdio.h>

int main(){
	int n,sum=0;
	scanf("%d",&n);
	int i;
	for (i=1;i<n;i++) {
	    sum=sum+((i*(i+1))/2);
	}
	printf ("%d",sum);
	return 0;
}