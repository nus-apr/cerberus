/*numPass=3, numTotal=5
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
1630758450
99
124
0
0
"
*/
#include <stdio.h>

int main() {
    int i,j,n1,n2,k;
    int ar1[20],ar2[20],ar3[40];
    scanf("%d",&n1);
    for(i=0;i<n1;i++)
    {
        scanf("%d",&ar1[i]);
    }
    scanf("%d",&n2);
    for(j=0;j<n2;j++)
    {
        scanf("%d",&ar2[j]);
    }
    for(i=0,j=0;i<n1&&j<n2;k++)
    {
        if(ar1[i]>=ar2[j])
        {
            ar3[k]=ar2[j];
            j++;
        }
        else
        {
            ar3[k]=ar1[i];
            i++;
        }
    }
    if(i<=n1)
    {
        for( ;j<n2;j++,k++)
        {
            
            
                ar3[k]=ar2[j];
            
    
        }
    }
    else
    {
        for( ;i<n1;i++,k++)
        {
            
            
                ar3[k]=ar1[i];
            
        }
    }
    for(k=0;k<n1+n2;k++)
    {
        printf("%d\n",ar3[k]);
    }
    

    
    
    
	// Fill this area with your code.
	return 0;
}