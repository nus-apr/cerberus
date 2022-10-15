/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"-2142610804"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"348468994"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"719550210"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"2147479055"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"-1834795665"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"828045058"
*/
#include <stdio.h>
int main() 
{
    int a[30];
    int N,d,i;
    scanf("%d %d",&d,&N);
    int b[d];
    for(i=0;i<d;i++)
    {
        scanf("%d",&b[i]);
    }
    if((N>=0)&&(N<d))
    {
        a[N]=b[N];
        printf("%d",a[N]);
    }
    else
    {
        int j,k;
        for(k=d;k<=N;k++)
        {
            a[k]=0;
            for(j=k-d;j<k;j++)
            {
                a[k]=a[j]+a[k];
            }
        }
        printf("%d",a[N]);
    }
	return 0;
}