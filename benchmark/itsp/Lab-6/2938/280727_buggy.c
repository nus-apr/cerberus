/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"11
13
2
20
18
18
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"1
3
6
10
15
15
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"2
6
5
0
2
7
4
3
-2
0
5
4198537
"
*/
#include <stdio.h>

int main() 
{
    int N,k,i,j;
    scanf("%d",&N);
    int A[N];
    int sum[20];
    for(i=0;i<(N-1);i++)
    {
        scanf("%d",&A[i]);
    }
    scanf("%d",&k);
    for(i=0;i<(N-k+1);i++)
    {
        sum[i] = 0;
    }
    for(i=0;i<(N-k+1);i++)
    {
        for(j=i;j<(i+k);j++)
        {
            sum[i] = sum[i] + A[j];
            printf("%d\n",sum[i]);
        }
    }
	return 0;
}