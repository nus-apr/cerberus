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
    int n,c,i=-1,m,t=-1,z;
    int*a;
    scanf("%d",&n);
    a=(int*)malloc(n*sizeof(int));
    for(int k=0;k<n;k++)
    {
        scanf("%d",&a[k]);
    }
    
   // c=getchar();
    while(i<n-1)
    {
        i++;
        //a[i]=c;
        for( t=i-1;t>=0;t--)
        {
            
            if(a[i]>a[t])
            {
                break;
            }
            
        }
        m=a[i];
        z=t;
        
        
        for(int j=i-1;j>t;j--)
        {
            a[j+1]=a[j];
        }
        a[z+1]=m;
        //printf("%d\n",a[]);
       // i++;
        //c=getchar();
    }
    for(int p=0;p<n;p++)
    {
        printf("%d ",a[p]);
    }
}