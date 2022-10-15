/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"89
69
-1091849832
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"31
22
1515913316
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"15
20
4198902
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"53
65
182961933
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"2
5
7
8
"
*/
#include <stdio.h>
void cal_sum(int arr[],int size,int k)
{
    int p1=0,sum=0;
    for(int i=1;i<=(size-k+1);i++)
    {
        for(int j=p1;j<=(p1+k);j++)
        {
            sum=sum+ arr[j];
        }
        printf("%d",sum);
        printf("\n");
        p1++;
        sum=0;
    }
}
int main() {
    int n,k;
    scanf("%d",&n);
    int A[n];
    for(int i=0;i<n;i++)
    {
        scanf("%d",&A[i]);
    }
    scanf("%d",&k);
    cal_sum(A,n,k);
	return 0;
}