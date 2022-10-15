/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2*
*1
", Output:"2*
*1"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"432*
43*1
4*21
*321
", Output:"
432*
43*1
4*21
*321"
Verdict:ACCEPTED, Visibility:1, Input:"5", ExpOutput:"5432*
543*1
54*21
5*321
*4321
", Output:"
5432*
543*1
54*21
5*321
*4321"
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"*
", Output:"*"
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
", Output:""
*/
#include<stdio.h>

int main(){
int x;
scanf("%d",&x);
    switch (x){
        case 1:printf("*");break;
        case 2:printf("2*");
               printf("\n*1");break;
        case 3:printf("32*");
                printf("\n3*1");
                printf("\n*21");break;
        case 4:printf("\n432*");
                printf("\n43*1");
                printf("\n4*21");
                printf("\n*321");break;
        case 5:printf("\n5432*");
                printf("\n543*1");
                printf("\n54*21");
                printf("\n5*321");
                printf("\n*4321");break;
    }
	return 0;
}