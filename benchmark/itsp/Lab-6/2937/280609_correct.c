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

int main() 
{   int A[50],B[50],C[100],n1,n2;
    scanf("%d",&n1);
    for(int i=0;i<n1;i++)
    {scanf("%d",&A[i]);
    }
    scanf("%d",&n2);
    for(int j=0;j<n2;j++)
    {scanf("%d",&B[j]);
    }
for(int i=0,k=0;i<n1,k<n1+n2;i++,k++)
    {  
        C[k]=A[i];
    }
for(int j=0,k=n1;j<n2,k<n1+n2;j++,k++)
    {   
        C[k]=B[j];
    }
for(int k=0;k<n1+n2;k++)
    {   for(int l=k+1;l<n1+n2;l++)
        {   if(C[l]<C[k])
            {   int temp=C[l];
                C[l]=C[k];
                C[k]=temp;
            }
        }
    }


for(int k=0;k<n1+n2;k++)
{   printf("%d\n",C[k]);
}
    	return 0;
}