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
void merge(int ar1[],int s1,int ar2[],int s2)
{
    int i=0,j=0,k;
    while((i<s1)&&(j<s2))
    {
        if(ar1[i]<ar2[j])
        {
            printf("%d\n",ar1[i]);
            i=i+1;
        }
        else
        if(ar1[i]==ar2[j])
        {
            printf("%d\n%d\n",ar1[i],ar2[j]);
            i=i+1;
            j=j+1;
        }
        else
        {
            printf("%d\n",ar2[j]);
            j=j+1;
        }
    }

    if(i<=s1)
    {
        for(k=i;k<s1;k++)
        {
            printf("%d\n",ar1[k]);
        }
    }
    if(j<=s2)
    {
        for(k=j;k<s2;k++)
        {
            printf("%d\n",ar2[k]);
        }
    }
}
int main() 
{
	int size1,size2,i;
	scanf("%d\n",&size1);
	int arr1[size1];
	for(i=0;i<size1;i++)
	{
	    scanf("%d ",&arr1[i]);
	}
	scanf("%d\n",&size2);
	int arr2[size2];
	for(i=0;i<size2;i++)
	{
	    scanf("%d ",&arr2[i]);
	}
	merge(arr1,size1,arr2,size2);
	return 0;
}