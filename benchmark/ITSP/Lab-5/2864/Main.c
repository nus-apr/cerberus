/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code
- Indentation: align your code properly
- Use the function in the template compulsorily and more functions, if necessary.
---------------------------------
Given two positive integers, n1 and n2, output all the prime numbers between (and including) n1 and n2, separated by a space each.

e.g.

Input:
11 20
Output:
11 13 17 19


Input:
3 11
Output:
3 5 7 11

Input:
4 10
Output:
5 7
*/
#include<stdio.h>
int check_prime(int num);
int main(){
   int n1,n2,i,flag;
   scanf("%d %d",&n1, &n2);
   for(i=n1;i<=n2;++i)
   {
      flag=check_prime(i);
      if(flag==0)
         printf("%d ",i);
   }
   return 0;
}
int check_prime(int num) /* User-defined function to check prime number*/
{
    if(num==1){
        return 1;
    }
   int j,flag=0;
   for(j=2;j<=num/2;++j){
        if(num%j==0){
            flag=1;
            break;
        }
   }
   return flag;
}