/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>

int max (int,int);                          // function declaration
void scanarray (int[],int);                 // function declaration

int main()
{
    int A[20],n,MaxTill[20],i,j,maxm=0;
    scanf("%d",&n);
    scanarray(A,n);
    for (i=0;i<n;i++)
    {
        MaxTill[i]=1;
        for (j=0;j<i;j++)
        {
            if (A[i]>A[j])
            {
                MaxTill[i]=max(MaxTill[i],(MaxTill[j]+1));
            }
        }
    }
    for (i=0;i<n;i++)
    {
        maxm=max(maxm,MaxTill[i]);
    }
    printf("%d",maxm);
    return 0;
}
    
    
    
    
    
    
    
    
    
    /*      Function Definition  :- to return maximum       */
int max (int a, int b)                      // arguments
{
    if (a > b)                              // if a is max
        return a;                           // return a
    else                                    // otherwise
        return b;                           // return b
}

    /*       Function definition :- to input the array       */
void scanarray (int A[],int n)              // arguments
{
    for (int i=0;i<n;i++)                   // loop for n elements
    {
        scanf("%d",&A[i]);                  // input element
    }
}