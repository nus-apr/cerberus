/*numPass=3, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"2 -3 2 ", Output:"2 -3 2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"20", ExpOutput:"20 15 10 5 0 5 10 15 20 ", Output:"20 15 10 5 0"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"4 -1 4 ", Output:"4 -1 4 "
Verdict:ACCEPTED, Visibility:0, Input:"16", ExpOutput:"16 11 6 1 -4 1 6 11 16 ", Output:"16 11 6 1 -4 1 6 11 16 "
*/
#include <stdio.h>
int N;
void revprint(int n){
    if(n==N) printf("%d ",n);
    else {
        printf("%d ",n);
        revprint(n+5);
    }
}
void print(int n){
    if(n<0) {printf("%d ",n);return revprint(n+5);}
    if(n==0){printf("%d",n);}
    else {
    printf("%d ",n);
    print(n-5);
}
        
    }
int main(){
    scanf("%d",&N);
    print(N);
	return 0;
}