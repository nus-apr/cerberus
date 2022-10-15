/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"4", Output:"5"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"20", Output:"14"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10", ExpOutput:"220", Output:"65"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"10", Output:"9"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"1", Output:"2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20", ExpOutput:"1540", Output:"230"
*/
#include<stdio.h>

int main(){
    int i,j,k,sum=0;
    scanf("%d",&j);
    for(i=1;i<=j;i++){
    for(k=1;k<=i;k++);    
        sum = sum + k;
    }
	printf("%d",sum);
	//Enter your code here
	return 0;
}