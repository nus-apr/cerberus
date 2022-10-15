/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"19457"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-1365"
Verdict:ACCEPTED, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"55312397"
Verdict:ACCEPTED, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-341"
*/
#include <stdio.h>
int recurr(int x[],int y,int t)
{
    int a[t],i,p,m=0;
    for(i=0;i<=t;i++)
    {
     if(i>=0&&i<y)
      {
        a[i]=x[i];
      }
     else
      {p=1;
        a[i]=0;
        while(p<=y)
        {
            a[i]=a[i]+a[i-p];
            p++;
        }
      }
    } 
  return(a[t]);    
}
int main() {
	int d,n,i,b[20];
	scanf("%d %d",&d,&n);
	
	for(i=0;i<d;i++)
	{
	    scanf("%d ",&b[i]);
	}
	printf("%d",recurr(b,d,n));
	
	return 0;
}