/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"4", Output:"6"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"20", Output:"15"
Verdict:WRONG_ANSWER, Visibility:1, Input:"10", ExpOutput:"220", Output:"66"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"10", Output:"10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1", ExpOutput:"1", Output:"3"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20", ExpOutput:"1540", Output:"231"
*/
#include<stdio.h>

    int main() {
    int i,n,T=0;
    
    scanf("%d",&n);
    
    for (i=0;i<=n;i=i+1);
        
    T=T+(i*(i+1)/2);
    
    printf("%d",T);
    
    return 0;
}