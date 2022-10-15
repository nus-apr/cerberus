/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"14", ExpOutput:"17
", Output:"17"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"29
", Output:"29"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"2
", Output:"21"
Verdict:ACCEPTED, Visibility:1, Input:"68", ExpOutput:"71
", Output:"71"
Verdict:ACCEPTED, Visibility:0, Input:"99", ExpOutput:"101
", Output:"101"
Verdict:ACCEPTED, Visibility:0, Input:"150", ExpOutput:"151
", Output:"151"
Verdict:ACCEPTED, Visibility:0, Input:"200", ExpOutput:"211
", Output:"211"
*/
#include<stdio.h>
#include<math.h>    //to optimise the program
int check_prime(int num){
       int i;
       for(i=2;i<=sqrt(num);i++)
       {
       if(num%i==0)
       return 0;
       }
        return 1;
       }
       
       
int main(){
    
    int N,i;
    scanf("%d",&N);
    if(N==1){
        printf("%d",N+1);
    }
    for(i=N;i<=N*N;i++){
    if (check_prime(i)){
    break;}
    }
    printf("%d",i);
    return 0;
}