/*numPass=6, numTotal=7
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"2"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>

int incsubseq (int[],int,int);
int incsubseq (int A[20],int n,int i)
{
    i=0;
    int j,k,max,cnt=1;
    max=A[i];
    for(j=i+1;j<n;j++)
    {
        if (A[j] > max)
        {
            cnt++;
            max=A[j];
        }
    }
    return cnt;
}  

int main() 
{
	int A[20],n,i,j,cnt,max=0,tmp;
	scanf("%d",&n);
	for(i=0;i<n;i++)
	{
	    scanf("%d",&A[i]);
	}

	for (i=0;i<n;i++)
	{
        cnt=incsubseq(A,n,i);	
	    if (cnt>max)
	        max=cnt;
	}
    printf("%d",max);
    return 0;
}

  
