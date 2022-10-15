/*numPass=3, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"4 5 5 5 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 2 3 3 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"1 3 4 4 4 4 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"1 3 4 4 4 4 4 4 4 4 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"1 3 4 4 4 4 4 4 4 4 4 "
*/
#include <stdio.h>
#include <stdlib.h>
void sort(int arr[],int n,int i)
{
    int j=0,temp;
    while(arr[j]<arr[i])
    {
        j++;
    }
    temp=arr[i];
    for(i=j+1;i<n;i++)
    {
        arr[i]=arr[i-1];
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