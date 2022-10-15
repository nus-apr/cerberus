/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>
int l;
int max(int A[],int size)
{
    int result=A[0];
    for (l=1;l<size;l++)
    {
        if (result<A[l])
        {
            result=A[l];
        }
        
    }
    return result;
}
int main() {
int size,val,i,j,k,m;
int Z[20];
int count[20];
scanf("%d",&size);
for (m=0;m<size;m++)
{
    count[m]=0;
}
for (i=0;i<size;i++)
{
    scanf ("%d",&val);
    Z[i]=val;
}



for (j=0;j<size-1;j++)
{
    int maximum=Z[j];
    for (k=j+1;k<size;k++)
    {
        
        if (maximum<Z[k])
        {
            count[j]++;
            maximum=Z[k];
        }
    }
}
printf("%d",max(count,size)+1);
// Fill this area with your code.
	return 0;
}