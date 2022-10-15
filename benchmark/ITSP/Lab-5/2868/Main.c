/*
ANNOUNCEMENT:
Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code 
- Indentation: align your code properly 
- Use the function in the template compulsorily and more functions, if necessary. 
-----------------------------------
Given a positive integer N, count the number of unique positive integer pairs {p1,p2} such that:
0<= p1 <= N
0<= p2 <= N
p1 + 2 = p2
p1 and p2 are primes

e.g.
Input: 11
Output: 2
Explanation: There are two twin prime pairs below 11: {3,5} and {5,7}

Input: 19
Output: 4
Explanation: There are four twin prime pairs below 19: {3,5}, {5,7}, {11,13} and {17,19}
*/
#include<stdio.h>
int check_prime(int num);
int main(){
   int n,i;
   scanf("%d",&n);
   int count = 0;
   for(i=2;i<=(n-2);++i)
   {
      if(!check_prime(i) && !check_prime(i+2)){
        count++;
      }
   }
   printf("%d\n",count);
   return 0;
}

int check_prime(int num) /* User-defined function to check prime number*/
{
    if(num==1)
        return 1;
   int j,flag=0;
   for(j=2;j<=num/2;++j){
        if(num%j==0){
            flag=1;
            break;
        }
   }
   return flag;
}