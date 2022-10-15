/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2*
*1
", Output:"2*
*1
"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"432*
43*1
4*21
*321
", Output:"432*
43*1
4*21
*321
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
Verdict:ACCEPTED, Visibility:0, Input:"1", ExpOutput:"*
", Output:"*
"
Verdict:ACCEPTED, Visibility:0, Input:"10", ExpOutput:"1098765432*
109876543*1
10987654*21
1098765*321
109876*4321
10987*54321
1098*654321
109*7654321
10*87654321
*987654321
", Output:"1098765432*
109876543*1
10987654*21
1098765*321
109876*4321
10987*54321
1098*654321
109*7654321
10*87654321
*987654321
"
*/
#include<stdio.h>

int main(){
    
    int i,j,N;
    
    scanf("%d",&N);
    
    i=1;
    
    j=N;
    
    while(i<=N)
    {
        while(j>0&&j>i)
        {
            printf("%d",j);
            
            j=j-1;
        }
        printf("*");
        
        j=i-1;
        
        while(j>0)
        {
            printf("%d",j);
            
            j=j-1;
        }
        i=i+1;
        
        j=N;
        
        printf("\n");
        
        
    }
	return 0;
}