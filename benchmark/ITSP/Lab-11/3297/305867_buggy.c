/*numPass=3, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"1 2 3 4 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"5 4 3 2 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"1 3 2 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"1 4 3 2 1 0 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"1 4 3 2 1 0 5 8 100 110 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"1 4 3 2 1 0 5 8 100 110 -10 "
*/
#include<stdio.h>
#include<stdlib.h>
void shift(int *a,int start,int stop)
{
    for(int i=stop-1;i>=start;i--)
        {
            a[i+1]=a[i];
        }
    return;
    
}

void insertionsort(int *a,int n)
{
    for(int i=1;i<n;i++)
        {
            if(a[i]>a[i-1])
                {
                    int j;
                    for(j=0;j<i;j++)
                        {
                            if(a[j]>a[i])
                            break;
                        }
                    int c=a[i];
                    shift(a,j,i);
                    a[j]=c;
                }
        }
        
    for(int i=0;i<n;i++)
        {
            printf("%d ",a[i]);
        }
        return;
}

int main()
{
    int n;
    scanf("%d \n",&n);
    int *a;
    a=(int*)malloc(sizeof(int)*n);
    for(int i=0;i<n;i++)
        {
            scanf("%d ",&a[i]);
        }
    insertionsort(a,n);
    return 0;
}
