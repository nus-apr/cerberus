/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2
3 1 -5
0 -2 4
", ExpOutput:"4
0 -6 10 14 -20 ", Output:"4
-15 0 0 0 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 4
2 -4 4 3 -1 6
1 -2 -5 2 4

", ExpOutput:"9
2 -8 2 19 -27 -15 15 -20 8 24 ", Output:"9
12 -22 16 20 15 -26 -15 0 0 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"15 15 
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 ", Output:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0 0 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 10
100 100 -200 -300 421 535 125 -235 122 -555 99
100 100 -200 -300 421 535 125 -235 122 -555 99

", ExpOutput:"20
10000 20000 -30000 -100000 64200 311200 53600 -488600 -216359 382870 392475 104480 160299 -454920 -424767 -90160 300484 -181950 332181 -109890 9801 ", Output:"20
9900 19900 200 -59700 -58321 117165 323575 30335 -476522 -216359 493870 483675 -137320 -133101 71790 85725 -57340 14884 0 0 "
*/
#include <stdio.h>

int main() {
	int n1,n2,a[20],b[20];
	scanf("%d %d\n",&n1,&n2);
	
	for(int i=1;i<n1+1;i++)
	{
	    scanf("%d ",&a[i-1]);
	}
	
	scanf("\n");
	for(int j=1;j<n2+1;j++)
	{
	    scanf("%d",&b[j-1]);
	}
	printf("%d\n",n1+n2);
	int m[40];
	
	for(int q=0;q<n1+n2;q++)
	{
	    m[q]=0;
	}
	for(int k=0;k<n1-1;k++)
	{
	  for(int l=0;l<=n2-1;l++)
	  {
	   m[k+l]=m[k+l]+(a[k]*b[l]);   
	  }
	}
	
	for(int z=0;z<n1+n2;z++)
	{
	    printf("%d ",m[z]);
	}
	return 0;
}