/*numPass=2, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"5"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:""
Verdict:ACCEPTED, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"8"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:""
*/
#include <stdio.h>

int main() {
    int i,d,n;
    i=0;
	int a[i];
	int b[i];
	scanf("%d %d",&d,&n);
	for(i=0;i<d;i++)
	{
	    scanf("%d",&b[i]);
	}
	for(i=0;i<=n;i++)
	{
	    if(n<d){
	    a[i]=b[i];}
	    else
	    for(i=d;i<=n;i++)
	        {
	            a[i]=0;
	            for(int j=(i-1);j>=(i-d);j--)
	            {
	                a[i]+=a[j];
	            }
	        }
	    printf("%d",a[i-1]);
	}
	return 0;
}