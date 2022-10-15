/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>

int main()
{
  int n,j,p,i,k=0;
  scanf("%d",&n);
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
         {
           k=1;     
          printf("YES");
          break;
         } 
      }  
        if (k==1)
        {break;}
        if ((j==n-2)&&(a[j]!=a[n-1]))
        printf("NO");
    }
      
        
      
      
	return 0;
}