/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"2 2
3 1 -5
0 -2 4
", ExpOutput:"4
0 -6 10 14 -20 ", Output:"4
0 -6 10 14 -20 "
Verdict:ACCEPTED, Visibility:1, Input:"5 4
2 -4 4 3 -1 6
1 -2 -5 2 4

", ExpOutput:"9
2 -8 2 19 -27 -15 15 -20 8 24 ", Output:"9
2 -8 2 19 -27 -15 15 -20 8 24 "
Verdict:ACCEPTED, Visibility:1, Input:"15 15 
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 ", Output:"30
1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 "
Verdict:ACCEPTED, Visibility:0, Input:"10 10
100 100 -200 -300 421 535 125 -235 122 -555 99
100 100 -200 -300 421 535 125 -235 122 -555 99

", ExpOutput:"20
10000 20000 -30000 -100000 64200 311200 53600 -488600 -216359 382870 392475 104480 160299 -454920 -424767 -90160 300484 -181950 332181 -109890 9801 ", Output:"20
10000 20000 -30000 -100000 64200 311200 53600 -488600 -216359 382870 392475 104480 160299 -454920 -424767 -90160 300484 -181950 332181 -109890 9801 "
*/
#include <stdio.h>

int main() {
    int n1,n2;
	scanf("%d %d",&n1,&n2);
	int a[17],b[17],c[35];/*a is the co efficients of 1st polynomial and b is the co efficient of 2nd polymnomial c is co efficient of 3 polynomial*/
	for(int d=0;d<=n1;d++)
	{
	    scanf("%d ",&a[d]);
	}
	for(int c=0;c<=n1;c++)
	{
	    scanf("%d ",&b[c]);
	}
	
	for(int k=0;k<=(n1+n2);k++){
	    c[k]=0;
	}
	for(int i=0;i<=(n1+n2);i++)
	{
	 for(int j=0;j<=i;j++)
	 { if(j>n1||(i-j)>n2)continue;
	     c[i]=c[i]+(a[j]*b[i-j]);
	 }  
	}
	c[n1+n2]=a[n1]*b[n2];
	printf("%d\n",n1+n2);
	for(int h=0;h<=(n1+n2);h++){
	 printf("%d ",c[h]);   
	}
	return 0;
}