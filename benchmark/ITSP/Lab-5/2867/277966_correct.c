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
    int i,j,k,sum=0;
    scanf("%d",&j);
    for(i=1;i<=j;i++){
        //sum of the number till starting from 1 to that no.
    for(k=1;k<=i;k++)    
        sum = sum + k;
        //total sum
    }
	printf("%d",sum);
	
	return 0;
}