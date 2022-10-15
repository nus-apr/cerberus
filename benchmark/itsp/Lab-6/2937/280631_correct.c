/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"5
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
21
"
Verdict:ACCEPTED, Visibility:1, Input:"2
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
12
31
45
"
Verdict:ACCEPTED, Visibility:1, Input:"5
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
10
"
Verdict:ACCEPTED, Visibility:0, Input:"3
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
7
9
"
Verdict:ACCEPTED, Visibility:0, Input:"5
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
1
2
3
4
5
"
*/
#include <stdio.h>

void merge (int A1[], int l1, int A2[], int l2, int A[])
{
    int i=0,j=0,count=0;
    while (count<l1+l2)
    {
        if (A1[i]<A2[j])
        A[count++]=A1[i++];
        if (A2[j]<A1[i])
        A[count++]=A2[j++];
        if (A1[i]==A2[j])
        {
            A[count++]=A1[i++];
            A[count++]=A2[j++];
        }
        if (i==l1)
        {
            while (j!=l2)
            A[count++]=A2[j++];
        }
        if (j==l2)
        {
            while (i!=l1)
            A[count++]=A1[i++];
        }
    }
}

int main()
{
    int N1,N2,i;
    scanf("%d", &N1);
    int C1[N1];
    for (i=0;i<N1;i++)
    scanf("%d", &C1[i]);
    scanf("%d", &N2);
    int C2[N2];
    for (i=0;i<N2;i++)
    scanf("%d", &C2[i]);
    int C[N1+N2];
    merge(C1,N1,C2,N2,C);
    for (i=0;i<N1+N2;i++)
    printf("%d\n", C[i]);
    return 0;
}