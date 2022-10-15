/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"4874377"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"0"
*/
#include <stdio.h>

int main() {
     int d,i,N,j;
     int p=0;
     scanf("%d %d",&d,&N);
     int a[31],b[21];
     for (i=0;i<d;i++)
        {
            scanf("%d",&b[i]);
            a[i]=b[i];
            p = p+a[i];
        }
        if(N < d)
            printf("%d", a[N]);
    else
    {
          a[d]=p;

        for (i=d+1;i<=N;i++) 
            {
                    a[i] = 0;
                    for(j=i-1;j>=i-d;j--)
                    {
                        a[i]=a[i]+a[j];
                    }    
            }
           printf("%d",a[i]);
    } 
	return 0;
}