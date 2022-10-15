/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code
- Indentation: align your code properly
- Use the function in the template compulsorily and more functions, if necessary.
---------------------------------

Given a positive integer N, output whether N can be expressed as a sum of two prime numbers.

e.g.
Input: 9
Output: Yes
Explanation: 9 = 7 + 2

Input: 11
Output: No
Explanation: There do not exist positive integers, x and y such that x+y=11 and x and y are prime numbers.
*/
#include <stdio.h>
int check_prime(int n);
int main()
{
    int n, i;
    scanf("%d",&n);
    for(i=2; i<=n/2; ++i)
    {
        if (check_prime(i)!=0)
        {
            if ( check_prime(n-i)!=0)
            {
                printf("Yes\n");
                return 0;
            }

        }
    }
    printf("No\n");
    return 0;
}
int check_prime(int n)      /* Function to check prime number */
{
    if(n==1)
        return 1;
        
    int i, flag=1;
    for(i=2; i<=n/2; ++i)
       if(n%i==0)
          flag=0;
    return flag;
}