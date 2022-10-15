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
", Output:"14
13
20
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"18
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
", Output:"5
7
"
*/
#include <stdio.h>
int main() {
    int a[20];
    int N;
    int i;
    scanf("%d",&N);
    for(i=1;i<N;i++)
    {
        scanf("%d",&a[i]);
    }
int sum,l,j,k;
scanf("%d",&k);

for(j=0;j<=N-k;j++)
{
    sum=0;
    for(l=0;l<k;l=l+1)
    {
        sum=sum+a[j+l];
    }
    printf("%d\n",sum);
    
    
}
	return 0;
}