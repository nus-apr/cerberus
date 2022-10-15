/*numPass=1, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2*
*1
", Output:"5432*
543*1
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"432*
43*1
4*21
*321
", Output:"5432*
543*1
54*21
5*321
"
Verdict:ACCEPTED, Visibility:1, Input:"5", ExpOutput:"5432*
543*1
54*21
5*321
*4321
", Output:"5432*
543*1
54*21
5*321
*4321
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"*
", Output:"5432*
"
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
", Output:"5432*
543*1
54*21
5*321
*4321
54321
54321
54321
54321
54321
"
*/
#include<stdio.h>

int main(){
    int n;
    scanf("%d",&n);
    for (int i=1; i<=n; i++) {
        for (int k=5; k>=1; k--) {
            if (k==i) {printf("*");}
            else {printf("%d",k);}
        }
    printf("\n");
    }
	
	return 0;
}