/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"5", ExpOutput:"55555
45555
34555
23455
12345
", Output:"55555
45555
34555
23455
12345
"
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"22
12
", Output:"22
12
"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"333
233
123
", Output:"333
233
123
"
Verdict:ACCEPTED, Visibility:1, Input:"6", ExpOutput:"666666
566666
456666
345666
234566
123456
", Output:"666666
566666
456666
345666
234566
123456
"
Verdict:ACCEPTED, Visibility:0, Input:"10", ExpOutput:"10101010101010101010
9101010101010101010
891010101010101010
78910101010101010
6789101010101010
567891010101010
45678910101010
3456789101010
234567891010
12345678910
", Output:"10101010101010101010
9101010101010101010
891010101010101010
78910101010101010
6789101010101010
567891010101010
45678910101010
3456789101010
234567891010
12345678910
"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"1
", Output:"1
"
*/
#include<stdio.h>

int main(){
    int N,i,j;
    scanf("%d",&N);
    for(i=1;i<=N;i++){
        for(j=1;j<=N;j++){
            if(j<i){
                printf("%d", N-i+j);
            }
            else{
                printf("%d", N); }}
                printf("\n");
    }
    
	
	return 0;
}