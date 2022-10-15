/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"18", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"0
", Output:"0"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"40", ExpOutput:"5
", Output:"5"
Verdict:ACCEPTED, Visibility:0, Input:"100", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"70", ExpOutput:"7
", Output:"7"
*/
#include<stdio.h>

int check_prime(int num){
   
     for(int i=2;i<=num;i++){
         if((num%i==0)&&(i!=num)){return 0;}
       if(i==num){return 1;}
     }
}
int main(){
    int N,num;
    int pair=0;
    scanf("%d",&N);
    for(num=2;num<=N-2;num++){
        if(check_prime(num)){
            if(check_prime(num+2)){
                pair=pair+1;
            }
        }
    }
    printf("%d",pair);
    return 0;
}