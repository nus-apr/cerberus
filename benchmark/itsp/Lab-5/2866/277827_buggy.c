/*numPass=7, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"89", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"59", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"Yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"131", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"123", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"125", ExpOutput:"No
", Output:"No"
Verdict:WRONG_ANSWER, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"No"
*/
#include<stdio.h>

int check_prime(int num){
    int i;
    for (i=2;i<num;i++){
        
        if (num%i!=0)
            continue;
        else
             break;
    }
     i=i-1;
        if (num%i!=0)
            return 1;//for prime
        else
            return 0;
}

int check_sum_of_primes (int a){
    
    int m; 
    int n ;
    for (m=2;m<a;m++){
            n=a-m;
         if(check_prime(m)&&check_prime(n))
             return 1;
         else
             continue;
    }
             return 0;
}


int main(){
	
	int p;
	scanf("%d",&p);
	
	     if (check_sum_of_primes(p)){
	         
	         printf("Yes");
	     } else {
	         
	         printf("No");
	     }
	         
	         
	return 0;
}