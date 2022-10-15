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
void insert(int*k,int n);
int main()
{ 
    int n;
    scanf("%d",&n);
    int *p=(int*)malloc(n*sizeof(int));
    for(int i=0;i<n;i++)
    {
        scanf("%d",&p[i]);}
    
    insert(p,n);
}
void insert(int* k,int n)
{   int c,d,t;
    for(c=1;c<=n-1;c++)
    {  
        d=c;
        while(d>0 && k[d]<k[d-1])
        {   
            t=k[d];
            k[d]=k[d-1];
            k[d-1]=t;
            d--;
        }
    }
    for(int j=0;j<n;j++)
    {
        printf("%d ",k[j]);
    }
}