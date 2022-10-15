/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"89", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:1, Input:"42", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:1, Input:"59", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:1, Input:"22", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"109", ExpOutput:"Yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"131", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"123", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"125", ExpOutput:"No
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"141", ExpOutput:"Yes
", Output:"yes"
*/
#include<stdio.h>

int check_prime(int num);

int check_prime(int num)
{   int i;
    int prime_or_not;
    int no_of_factors=0; //variable to store no of factors
    
    for(i=1;i<=num;i++)
    {
    if(num%i==0) //check if i is a factor of num
    no_of_factors++; //update if i is a factor of num
    }
    
    if(no_of_factors==2)
        prime_or_not=1; //num is prime 
    else
        prime_or_not=0; //num is not prime;
    
    return prime_or_not; // return 0 or 1 accordingly    
    }
    
    
int main(){
	       int N;
	       int no_is_prime=0;//variable to return 0 or 1  
	       int i; // variable to be used in for loop
	       
	       scanf("%d",&N); //input N
	       
	       for(i=2;i<=N-2;i++)
	    {
	      if(check_prime(i)==1) // check if i is prime
	    {
	       if(check_prime(N-i)==1) //check if N-i is prime
	       no_is_prime=1; // both i and N-i are prime
	    }
	    }
	    
	    if(no_is_prime)
	        printf("yes"); // no_is_prime=1
	    else
	        printf("no");  // no_is_prime=0
	    
	return 0;
}