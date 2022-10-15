/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:ACCEPTED, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 1 2 3 "
Verdict:ACCEPTED, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"0 1 1 2 3 4 "
Verdict:ACCEPTED, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"0 1 1 2 3 4 5 8 100 110 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:ACCEPTED, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"-10 0 1 1 2 3 4 5 8 100 110 "
*/
#include<stdio.h>
#include<stdlib.h>
int main()
{
    int *a,i,j,k,n,temp1;
    scanf("%d",&n);
    a=(int *)malloc(n*sizeof(int));
    for(i=0;i<n;i++)
    scanf("%d",&a[i]);
    for(i=1;i<n;i++)
    {
        if(a[i]>=a[i-1])
        continue;
        else
        for(j=0;j<i;j++)
        {
            if(a[j]>a[i])
            {
                temp1=a[i];
                for(k=i;k>j;k--)
                {
                    a[k]=a[k-1];
                    
                }
               a[j]=temp1; 
            }
        }
    }
    for(i=0;i<n;i++)
    printf("%d ",a[i]);
    
    
    
    
    
    
    return 0;
}