/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"5", ExpOutput:"55555
45555
34555
23455
12345
", Output:"455555
45555
4555
455
45
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"22
12
", Output:"122
12
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"333
233
123
", Output:"2333
233
23
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"666666
566666
456666
345666
234566
123456
", Output:"5666666
566666
56666
5666
566
56
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
", Output:"910101010101010101010
9101010101010101010
91010101010101010
910101010101010
9101010101010
91010101010
910101010
9101010
91010
910
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"1
", Output:"01
"
*/
#include<stdio.h>
int main(){
    int i=0;
    int N=1,j,k;
    scanf("%d",&N);
    for(i=0;i<N;i++)
    {
        for(j=1;j>0;j--)
        printf("%d",N-j);
        for(k=i;k<N;k++)
        printf("%d",N);
        printf("\n");
    }
	}