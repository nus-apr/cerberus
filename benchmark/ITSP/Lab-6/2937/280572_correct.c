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

int main() {
    int i,j,k;
    int a[20];
    int b[20];
    int c[40];
    int n1,n2;
    k=0;
    scanf("%d",&n1);
    for(i=0;i<n1;i=i+1)
    scanf("%d",&a[i]);
    scanf("%d",&n2);
    for(j=0;j<n2;j=j+1)
    scanf("%d",&b[j]);
    i=0,j=0;
    while((i<n1) && (j<n2))
    {
        if(a[i]<b[j])
        {
           c[k]=a[i]; 
           i=i+1;
           k++;
        }
        else
        {
            c[k]=b[j];
            j=j+1;
            k++;
        }
    }
        if(i<n1)
        {
         for( ;i<n1;i=i+1)
         {
            c[k++]=a[i];
         }
        }
        else
        {
         for( ;j<n2;j=j+1)
            {
            c[k++]=b[j];
            }
        }
        
     for(k=0;k<(n1+n2);k=k+1)
     {
        
        printf("%d\n",c[k]);
        
}	// Fill this area with your code.
	return 0;
}