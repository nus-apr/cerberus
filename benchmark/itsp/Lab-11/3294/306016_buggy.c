/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"8", ExpOutput:"8 3 -2 3 8 ", Output:"8 "
*/
#include <stdio.h>
int input,x=0;
void recurr(int n){
    if(n==input)
    printf("%d",n);
    return;
    printf("%d ",n);
    if(x==1){
        recurr(n+5);
    }
    else {if(n>0){
        recurr(n-5);
    }
    if(n<=0){
        x=1;
     recurr(n+5);
    } 
}
}


int main(){
    scanf("%d",&input);
    printf("%d ",input);
    recurr(input-5);
	return 0;
}