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
int prod[30];
int poly_n1[15],poly_n2[15];
int multiply_poly(int n1,int n2);
int print_poly(int n);
int main() {
	int n1,n2;
	scanf("%d %d",&n1,&n2);
	int i;
    for(i=0;i<=n1;i++)  
	{
	    scanf("%d ",&poly_n1[i]);
	}
	for(i=0;i<=n2;i++)
	{
	    scanf("%d ",&poly_n2[i]);
	}
    multiply_poly(n1,n2);
    print_poly(n1+n2);
	return 0;
}

int multiply_poly(int n1,int n2)
{
    int i,j;
    for(i=0;i<30;i++){
        prod[i]=0;}
    for(i=0;i<=n1;i++)
    {
        for(j=0;j<=n2;j++)
        {
            prod[i+j]=prod[i+j]+poly_n1[i]*poly_n2[j];
        }
    }
    return 0;
}

int print_poly(int n)
{
    int i;
    printf("%d\n",n);
    for(i=0;i<=n;i++){
        printf("%d ",prod[i]);}
    return 0;
}