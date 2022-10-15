/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"5", ExpOutput:"55555
45555
34555
23455
12345
", Output:"5
5
5
5
5
45
5
5
5
345
5
5
2345
5
12345
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"22
12
", Output:"2
2
12
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"333
233
123
", Output:"3
3
3
23
3
123
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"666666
566666
456666
345666
234566
123456
", Output:"6
6
6
6
6
6
56
6
6
6
6
456
6
6
6
3456
6
6
23456
6
123456
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"10101010101010101010
9101010101010101010
891010101010101010
78910101010101010
6789101010101010
567891010101010
45678910101010
3456789101010
234567891010
12345678910
", Output:"10
10
10
10
10
10
10
10
10
10
910
10
10
10
10
10
10
10
10
8910
10
10
10
10
10
10
10
78910
10
10
10
10
10
10
678910
10
10
10
10
10
5678910
10
10
10
10
45678910
10
10
10
345678910
10
10
2345678910
10
12345678910
"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"1
", Output:"1
"
*/
#include<stdio.h>

int main(){
	int N;/*defining N as a integer*/
	int i,j;
	scanf ("%d",&N);/*scanning value of N*/
	for (i=1;i<=N;i=i+1)
	{
	    for (j=1;j<=N;j=j+1)
	    if (i>j){
	        printf ("%d",N-i+j);
	    }
	    else 
	    {
	        printf ("%d\n",N);
	    }
	    
	}
	
	return 0;
}