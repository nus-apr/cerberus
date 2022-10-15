/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 5 9 16
3
3 5 21", ExpOutput:"1
2
3
5
5
9
16
21
", Output:"1
2
3
5
5
9
16
0
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2
1 2
3
12 31 45
", ExpOutput:"1
2
12
31
45
", Output:"1
2
45
0
4892160
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
2 4 6 8 10
5
1 3 5 7 9", ExpOutput:"1
2
3
4
5
6
7
8
9
10
", Output:"1
2
3
4
5
6
7
8
9
0
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
-1 2 5
4
1 3 7 9", ExpOutput:"-1
1
2
3
5
7
9
", Output:"-1
1
2
3
5
0
4224246
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 2 3 4 5
2
-1 0", ExpOutput:"-1
0
1
2
3
4
5
", Output:"-1
0
3
4
5
0
4197697
"
*/
#include <stdio.h>
void merge_array(int A[20],int sizeA,int B[20],int sizeB)
{
    int C[40],sizeC=sizeA+sizeB,i=0,markA=0,markB=0;
    while(markA<sizeA&&markB<sizeB)
    {
        if(A[markA]<B[markB])
        {
            C[i]=A[markA];
            markA++;
            i++;
        }
        else
        {
            C[i]=B[markB];
            markB++;
            i++;
        }
    }
    
    if(markA==sizeA)
    {
        for(;i<sizeC;i++)
        {
            C[i]=B[i];
        }
    }
    if(markB==sizeB)
    {
        for(;i<sizeC;i++)
        {
            C[i]=A[i];
        }
    }
    for(i=0;i<sizeC;i++)
	{
	    printf("%d\n",C[i]);
	}
}
int main() {
	// Fill this area with your code.
	int A[20],B[20],C[40],N1,N2,i;
	scanf("%d",&N1);
	for(i=0; i<N1; i++)
	{
	    scanf("%d",&A[i]);
	}
	scanf("%d",&N2);
	for(i=0; i<N2; i++)
	{
	    scanf("%d",&B[i]);
	}
	merge_array(A,N1,B,N2);
	
	
	return 0;
}