/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"1 2 3 1 2 3 1 2 3 3 0 1 2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"1 3 6 10 10 30 47 62 -10 -29 -31 -32 0 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 2 3 4 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"-1 -3 -6 -4 -9 -15 -7 -15 -24 0 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"-1 -2 -3 -1 -2 -3 -1 -2 -3 0 "
*/
#include <stdio.h>

int main() {
	int a[100][100],i,j,n,m;
	int sum[100];
	for(int k=0;k<100;k++)
	sum[k]=0;
	scanf("%d %d",&n,&m);
	for(i=0;i<n;i++)
	{
	    for(j=0;j<m;j++)
	    {
	        scanf("%d",&a[i][j]);
	        sum[i]=sum[i]+a[i][j];
	        printf("%d ",sum[i]);
	    }
	}
	int max;
	for(i=0;i<n;i++)
	{
	    if(sum[i]>=sum[i+1])
	    max=sum[i];
	    else
	    max=sum[i+1];
	}
	printf("%d ",max);
	for(i=0;i<n;i++)
	{
	    if(sum[i]==max)
	    printf("%d ",i);
	}
	return 0;
}