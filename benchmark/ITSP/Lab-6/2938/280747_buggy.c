/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"47
55
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"13
20
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"10
14
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"41
51
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
"
*/
#include <stdio.h>

int main() {
	// Fill this area with your code.
	int n,i,j,k;
	scanf("%d\n", &n);
	int a[n]; 
	for(i=0;i!=n;i++) scanf("%d ",&a[i]);
	scanf("\n%d",&k);
	for(i=0;i<n-k;i++) {
	    int sum=0; 
	    for(j=i; j!=i+k; j++) {
	        sum+=a[j]; 
	    }
	   printf("%d\n", sum);
	}
	return 0;
}