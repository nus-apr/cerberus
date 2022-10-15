/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"18", ExpOutput:"3
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"0
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"24", ExpOutput:"4
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"40", ExpOutput:"5
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"100", ExpOutput:"8
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"70", ExpOutput:"7
", Output:""
*/
#include<stdio.h>

int check_prime(int num);
int main(){
int t,num,N;
for(int i=2;i<=(num/2);i=i+1){
    if(num%i==0){ // if the number is completely divided
    t=1;
    break;
    }    
    else   // if the number is not completely divided
    t=0;
    }
    if(t == 1){return 1;}
    else {return 0;}
    scanf("%d",&N); 
    int count=0;
    int p;
    for(p=3;p<=N-2;p=p+2){
        if(check_prime(p)==0 && check_prime(p+2)==0){
            count=count+1;
        } 
    }
     printf("%d",count);
    return 0;
}
