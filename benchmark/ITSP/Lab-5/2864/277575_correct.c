/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:ACCEPTED, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>

int check_prime(int num){

    for (int j=2 ; j<num ; j++){
        if(num%j==0){
            break ;
        }
        if(num%j!=0){
            if (j==num-1){
               printf("%d ",num) ;
            }
        }
    }
}
int main(){
    int n1 , n2 , num, j;
    scanf("%d %d",&n1 , &n2);
    if (n1 <=2){
        printf ("%d ",2);
    }
    for (num = n1 ; num <=n2 ; num++){
    check_prime(num);
    }

    return 0 ;
}