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
#include <stdio.h>
#include <stdlib.h>
void sort(int arr[],int n,int i)
{
    int j=0,temp,k;
    while(arr[j]<arr[i])
    {
        j++;
    }
    temp=arr[i];
    for(k=i;k>=j+1;k--)
    {
        
        arr[k]=arr[k-1];
    }
    arr[j]=temp;
}

int main()
{
    int *arr,n,i;
    scanf("%d\n",&n);
    arr=(int*)malloc(n*sizeof(int));
    for(i=0;i<n;i++)
    scanf("%d",&arr[i]);
    for(i=1;i<n;i++)
    {
        if(arr[i]>arr[i-1])
        continue;
        else
        sort(arr,n,i);
    }
    for(i=0;i<n;i++)
    printf("%d ",arr[i]);
    return 0;
}