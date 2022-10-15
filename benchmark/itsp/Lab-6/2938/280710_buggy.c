/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"47
102
158
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"13
33
53
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"10
24
42
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"41
92
153
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"0
0
1
9
"
*/
#include <stdio.h>

int main() {
	int n;
	scanf("%d",&n);
	int A[n];
	for (int i=0;i<n;i++)  {
	    scanf("%d",&A[i]);
    }
    int k;
    int sum = 0;
    scanf("%d",&k);
    for (int j=0;j<=n-k;j++)  {
         for (int z=j;z<j+k;z++)  {
             sum = sum + A[z];
             
         }
         printf("%d",sum);
             printf("\n");
        }
	
	return 0;
}