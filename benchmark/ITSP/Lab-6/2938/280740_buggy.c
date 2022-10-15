/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"71
207337026
207369751
207369739
207369737
32769
2
4197697
4197697
4197698
4197698
4
4
207336939
207369706
211570318
211570318
8428374
8395607
4195026
4195030
4195030
4195030
8395636
8395632
11278552
11278552
11277236
11277236
4199324
4199324
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"24
204785518
204818267
204818267
204818265
32769
2
4197697
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:""
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
", Output:""
*/
#include <stdio.h>

int main() {

	int i,k,j;
	int N,sum=0,m;
	scanf("%d",&k);
	scanf("%d",&N);
	int array[20];
	for(i=0;i<=(N-1);i++)
	{scanf("%d",&array[i]);}
	
	for(m=0;m<=(N-k);m++){
	{for(j=m;j<=(m+k-1);j++)
	{sum=sum+array[j];
	    
	}}
	{printf("%d\n",sum);}
	sum=0;
	
	}
	return 0;
}