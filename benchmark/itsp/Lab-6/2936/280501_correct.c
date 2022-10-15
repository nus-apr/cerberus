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
int check(int a[],int n)
   { int i,j;
   for (i=0;i<n;i++)
      {for (j=1;j<n-i;j++)
        {if (a[i]==a[i+j])
        return 1;}}
        return 0;}
int main() {
	 int n,i,j;
	scanf("%d",&n);
	int a[n];
	for(i=0;i<n;i++)
	 { scanf("%d",&a[i]);}
	if (check(a,n)==1)
	  printf("YES");
	else if(check(a,n)==0)
	  printf("NO");
	return 0;
}