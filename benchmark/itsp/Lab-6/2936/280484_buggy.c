/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:""
*/
#include <stdio.h>

int main()
{
  int n,j,p,i;
  scanf("%d\n",&n);
  int a[n];
  for (i=0;i<n;i++)
  {
    scanf("%d",&a[i]);      
  }
    for (j=0;j<n-1;j++)
    {
      for (p=j+1;p<n;p++)
      {
        if (a[j]==a[p])
         printf("YES");
         break;
        if (j==n-2)
         {
           printf("NO");     
         }
      } 
    }
        
      
      
	return 0;
}