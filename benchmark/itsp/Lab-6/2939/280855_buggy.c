/*numPass=3, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"4"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"8"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"8"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"5"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>

int main() 
  {
  int n,i,p,j,k,m;
  scanf("%d",&n);
  int a[n];
  int MaxTill[n];
	for(i=0;i<n;i++)
	{
	    scanf("%d",&a[i]);
	}
        MaxTill[0]=1;
        for(j=0;j<n;j++)
    {
        MaxTill[j]=1;
        for(m=0;m<j;m++)
        {if(a[j]>a[m])
        {if(1+MaxTill[m]>MaxTill[j])
        {
            MaxTill[j]=MaxTill[m]+1;
        }}
    }}
    for(p=0;p<n;p++)
    {
        if(MaxTill[p]>m)
            m=MaxTill[p];
            
            
       
       
}
      printf("%d",m);
  }