/*numPass=2, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"47
55
56
"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"13
20
20
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"3
6
10
5
9
14
7
12
18
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"6
12
20
30
41
10
18
28
39
51
14
24
35
47
61
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"6
5
0
3
-2
0
-6
-4
1
-3
2
8
"
*/
#include <stdio.h>

int main() {
	int j,n,i,k,s,x;
	scanf("%d\n",&n);
	int a[n];
	for(i=0;i<n;i++){
	    scanf("%d ",&a[i]);
	}
	
	scanf("%d",&k);
	for(j=0;j<(n-(k-1));j++){
	    s=a[j];
	    for(x=j+1;x<j+k;x++){
	       s=s+a[x];
	       printf("%d\n",s);
	    }
	}
	
	
	
	
	
	return 0;
}