/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:ACCEPTED, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>
#include<math.h>

int check_prime(int num){
    int x;
    int i=3;
    int n=ceil(sqrt(num));
    if (!(num%2)){
        return 0;
    }else{
    while (i<=n){
        x=num%i;
        i=i+2;
        if (x==0){
            return 0;
        }else{
            continue;
        }
    }
    }
    return x;
}


int main(){
    int n1, n2;
    scanf("%d %d", &n1, &n2);
    int n=n1;
    while (n<=n2){
        if ((check_prime(n))||(n==2)||(n==3)){
            printf("%d ", n);
        }
        n++;
    }

    return 0;
}