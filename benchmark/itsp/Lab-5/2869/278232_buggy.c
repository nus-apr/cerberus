/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"5", ExpOutput:"55555
45555
34555
23455
12345
", Output:"5
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"22
12
", Output:"2
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"333
233
123
", Output:"3
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6", ExpOutput:"666666
566666
456666
345666
234566
123456
", Output:"6
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
"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"1
", Output:"1
"
*/
#include<stdio.h>

int main(){
	int i,j;

    int n;
    int k=n;
    scanf("%d",&n);
    
    
    for(i=n;i<=n;i=i+1) 
    {for(j=n;j<=n;j=j+1)
    {
    if(j<i){
        printf("%d",n-i+j);
    }
    else printf("%d",n);
        
    }
        printf("\n");
    }
    return 0;
}