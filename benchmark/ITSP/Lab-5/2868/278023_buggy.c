/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"18", ExpOutput:"3
", Output:"5"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"0
", Output:"2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"24", ExpOutput:"4
", Output:"6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"40", ExpOutput:"5
", Output:"7"
Verdict:WRONG_ANSWER, Visibility:0, Input:"100", ExpOutput:"8
", Output:"10"
Verdict:WRONG_ANSWER, Visibility:0, Input:"70", ExpOutput:"7
", Output:"9"
*/
#include<stdio.h>

int check_prime(int num)
{
int i;
    for(i=2;i<=num-1;i++){
        if (num%i==0){
            return 0;
        }
        else continue;
    }
    return 1;
}
int main(){
    int n;
    scanf("%d",&n);
    int count=0;
    int i=0;
    for(i=0;i<=n-2;i++){
        if ((check_prime(i))&&(check_prime(i+2))==1){
            count++;
        }
        
    }
    printf("%d",count);
    return 0;
}