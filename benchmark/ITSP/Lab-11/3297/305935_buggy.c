/*numPass=3, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"1 5 4 3 2 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 3 2 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"0 4 3 2 1 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"0 4 3 2 1 1 5 8 100 110 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"-10 4 3 2 1 1 5 8 100 110 0 "
*/
#include<stdio.h>
#include<stdlib.h>
void swap(int *ptra,int *ptrb)
{
    int temp;
    temp = *ptra;
    *ptra = *ptrb;
    *ptrb = temp;
}
int main()
{
    int n;
    scanf ("%d",&n);
    int *arr;
    arr = (int *)malloc (n*sizeof(int));
    int i,j;
    for (i=0;i<n;i++)
    {
        scanf("%d",&arr[i]);
    }
    for (i=1;i<n;i++)
    {
        for (j=0;j>=0;j--)
        {
            if (arr[j] > arr[i])
            {
                //t=arr[j];
               // for (k=i;k<=j-1;k++)
                //{
                //    arr[k+1] = arr[k];
               // }
               // arr[i] = t;
               swap(&arr[j],&arr[i]);
                i--;
               // break;
            }
            else {continue;}
        }
    }
    for(i=0;i<n;i++)
    {
        printf ("%d ",arr[i]);
    }
    return 0;
}