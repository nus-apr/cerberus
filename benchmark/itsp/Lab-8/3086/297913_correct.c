/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"5 8
0 1 0 1 0 1 0 1
0 0 0 0 0 0 0 0
0 0 0 1 1 1 0 0
0 0 0 1 1 1 0 0
0 0 0 1 1 1 0 0", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"4 3
1 1 1 
1 1 1
1 1 1
1 1 1
", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"3 3
0 0 0
0 0 0
0 0 0", ExpOutput:"0
", Output:"0"
Verdict:ACCEPTED, Visibility:0, Input:"2 5
0 0 0 0 0
1 1 1 1 1", ExpOutput:"1
", Output:"1"
Verdict:ACCEPTED, Visibility:0, Input:"2 5
0 1 0 1 0
1 0 1 0 1", ExpOutput:"1
", Output:"1"
*/
#include <stdio.h>
int min(int a,int b, int c)
{
    int small;
    if(a<=b&&a<=c)
        small= a;
    if(b<=a && b<=c)
        small= b;
    if(c<=a&&c<=b)
        small= c;
        //printf("small is %d\n",small);
        return small;
}

int main() {
	// Fill this area with your code.
	int n,m,a[20][20],i,j,sum[20][20],large;
	scanf("%d",&n);
	scanf("%d",&m);
	for(i=0;i<n;i++)
	{
	    for(j=0;j<m;j++)
	    {
	        scanf("%d",&a[i][j]);
	    }
	}
	large=a[0][0];
	    for(i=0;i<m;i++)
    {
        sum[0][i]=a[0][i];
    }
    for(i=1;i<n;i++)
    {
        sum[i][0]=a[i][0];
    }
    for(i=1;i<n;i++)
    {
        for(j=1;j<m;j++)
        {
            if(a[i][j]==0)
            {
                sum[i][j]=0;
            }
            else
            {
                sum[i][j]=1+min(sum[i-1][j],sum[i][j-1],sum[i-1][j-1]);
            }
        }
    }
    //printf("sum ele is %d\n",sum[4][5]);
    for(i=0;i<n;i++)
    {
        for(j=0;j<m;j++)
        {
            if(sum[i][j]>large)
            {
                large=sum[i][j];
            }
        }
    }
	printf("%d",large);
	return 0;
}