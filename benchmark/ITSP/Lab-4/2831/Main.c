/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include
- Comments for non trivial code 
- Indentation: align your code properly 
- Use of character constants instead of ASCII values ('a', 'b, ..., 'A', 'B', ..., '0', '1' etc instead of ASCII values like 65, 66, 48 etc.) 

You would be given a positive integer as an input. Write a program which prints the reversed number. (Use only the C constructs that have been covered in the lectures.)

Input:
12345
Output:
Reverse of 12345 is 54321
*/
#include <stdio.h>
int main()
{
  int n , m = 0;
  int old;
  scanf("%d", &n);

   old = n ;
    
  while(n > 0)
  {
  	  m = m*10;
  	  m = m + n%10;
      n/=10;             /* n=n/10 */
  }
  printf("Reverse of %d is %d", old, m);
}