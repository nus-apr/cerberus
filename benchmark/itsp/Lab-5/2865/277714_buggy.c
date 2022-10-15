/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2*
*1
", Output:"5432*543*1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"432*
43*1
4*21
*321
", Output:"5432*543*154*125*123"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5", ExpOutput:"5432*
543*1
54*21
5*321
*4321
", Output:"5432*543*154*125*123*1234"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"*
", Output:"5432*"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10", ExpOutput:"1098765432*
109876543*1
10987654*21
1098765*321
109876*4321
10987*54321
1098*654321
109*7654321
10*87654321
*987654321
", Output:"5432*543*154*125*123*1234*12345*123456*1234567*12345678*123456789"
*/
#include<stdio.h>

int main(){
	int N,i,j,k;
	scanf("%d",&N);
	for(i=1;i<=N;i++)
	{
	    for(j=5;j>i;j--){
	        printf("%d",j);
	    }
	    printf("*");
        
        for(k=1;k<i;k++){
            printf("%d",k);
        }	
	    
	}
	//Enter your code here
	return 0;
}