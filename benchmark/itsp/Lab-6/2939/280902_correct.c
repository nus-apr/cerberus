/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>

int max(int a,int b)
{
    return a>b?a:b;
}

int main() 
{
    int A[20],MaxTill[20],N;
    int i=0,j=0;
    scanf("%d",&N);
    for(i=0;i<N;i++)
    {
        scanf("%d",&A[i]);
    }
    for(i=0;i<N;i++)
        MaxTill[i]=1;
    int max=1;
    for(i=1;i<N;i++)
    {
        for(j=0;j<i;j++)
        {
            if(((MaxTill[j]+1)>=max)&&(A[i]>A[j]))
            {
                max=MaxTill[j]+1;
                MaxTill[i]=MaxTill[j]+1;
            }
        }
        //printf("%d\n",max);
    }
    printf("%d",max);
	return 0;
}