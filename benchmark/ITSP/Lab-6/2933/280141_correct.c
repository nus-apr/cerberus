/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14
2
13 42", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"6
1 2 3 4 5 6
3
3 2 1", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 6 1
2
1 6", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 3 5 7 9
2
2 4", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
9 9 8 9 9
2
9 9", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int main() {
    int N1,N2,i,j,cnt=1;// cnt does the counting part
    scanf("%d\n",&N1);
	int A1[N1];
	for(i=0;i<N1;i++)
	scanf("%d ",&A1[i]);
	scanf("\n%d\n",&N2);
	int A2[N2];
	for(j=0;j<N2;j++)
	scanf("%d ",&A2[j]);
	for(int k=0;k<N1;k++) 
	{
	    if(A2[0]==A1[k]) //if first element of A2 matches
	    {  
	        int s=1;
	         for(int m=k+1;m<N1-k;m++)
	         {
	             if(A2[s++]==A1[m++])
	             cnt=cnt+1;
	             else break;
	         }
	    }
	   
	}
	if(cnt==N2)  //if all elements are included
	printf("YES");
	else printf("NO");
	return 0;
}