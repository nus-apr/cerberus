/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"-2142610612"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"787633922"
Verdict:WRONG_ANSWER, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"1389778690"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"2147479055"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"-1696625297"
Verdict:WRONG_ANSWER, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-2122279166"
*/
#include <stdio.h>
int d,N;


int read_into_array(int t[],int size)
{
    int i;
    for(i=0;i<d;i++)
    {
        scanf("%d",&t[i]);
    }
    return 0;
}


int main() {
    
    scanf("%d %d\n",&d,&N);
    
    int b[d];
    
    read_into_array(b,d);
    
    int a[30];
    
    int i;
    for(i=0;i<d&&N<d;i++)
    {
        a[i]=b[i];
    }
    if(N<d)
    {
    printf("%d",a[N]);
    }
     else if(N>=d)
    {
        //a[d]=0;
        /*
        int p;
        for(p=0;p<=d;p++)
        {
            a[d]=a[d]+a[p];
        }
        int i;
        */
        for(i=d;i<=N;i++)
        {
            int j;
            a[i]=0;
            for(j=i-d;j<=i-1;j++)
            {
                
                a[i]=a[i]+a[j];
            }
            
        }
	    printf("%d",a[N]);
    }
    
	return 0;
}