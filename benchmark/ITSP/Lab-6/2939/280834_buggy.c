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
Verdict:WRONG_ANSWER, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"7"
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

int main() {
	int A[20];
	int N;
	int big;
	int a,i,k;
	scanf("%d",&N);
	for(a=0;a<N;a++)
	{
	    scanf("%d",&A[a]);
	}
    int Maxtill[N];
    Maxtill[0]=1;
    for(i=0;i<N;i++)
    {
        if(A[i+1]>A[i])
        {
            Maxtill[i+1]=Maxtill[i]+1;
        }
        else
        {
            Maxtill[i+1]=Maxtill[i];
        }
    }
    big=Maxtill[0];
    for(k=1;k<N;k++)
    {
        if(Maxtill[k]>big)
        big=Maxtill[k];
    }
    printf("%d",big);
	return 0;
}