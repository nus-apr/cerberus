/*
ANNOUNCEMENT: Up to 20% marks will be allotted for good programming practice. These include 
- Comments: for the non trivial part of the code 
- Indentation: align your code properly 
-Don't put extra whitespace anywhere.
 ---------------------------------
 
Given an integer N(N>0) as input,your program should output the following pattern: 
Example:

Input
5

Output
55555
45555
34555
23455
12345

Input 
2

Output
22
12

*/
#include <stdio.h>

int main()
{
  int n;
  scanf("%d",&n);
  int i, j, k;
  for(i=n;i>=1;i--)
  {
    k = i;
    for(j=1;j<=n;j++)
    {
      if(k <= n)
      {
        printf("%d",k);
      }
      else
      {
        printf("%d",n);
      }
      k++;
    }
  printf("\n");
  }
  return 0;
}
