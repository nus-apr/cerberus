/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"4", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"20", Output:"20"
Verdict:ACCEPTED, Visibility:1, Input:"10", ExpOutput:"220", Output:"220"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"10", Output:"10"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"1", Output:"1"
Verdict:ACCEPTED, Visibility:0, Input:"20", ExpOutput:"1540", Output:"1540"
*/
#include<stdio.h>

int main(){
    int N,i;int sum=0;
    scanf("%d",&N);
    for(i=1;i<=N;i++){
        sum+=i*(i+1)/2;
        
    
    }
    printf("%d",sum);
	//Enter your code here
	return 0;
}