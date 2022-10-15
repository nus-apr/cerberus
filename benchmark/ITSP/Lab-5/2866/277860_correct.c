/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"131", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"123", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"125", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"Yes"
*/
#include<stdio.h>

int check_prime(int num){
int i=2;
while(i<num){
    if(num%i==0)
    return 1;
    i=i+1;
} return 0;
}
int main () {
    int i;
    int N;
    int p=1;
    scanf("%d", &N);
    for(i=2;i<N;i++){
        int q= check_prime(i)+check_prime(N-i);
        if(q==0)
        {printf("Yes");
        return 0;}
        
    }
    printf("No");
	return 0;
}