/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4 4
1 2 3 4", ExpOutput:"10
", Output:"10"
Verdict:ACCEPTED, Visibility:1, Input:"5 0
55 32 56 12 83", ExpOutput:"55
", Output:"55"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1", ExpOutput:"19457
", Output:"19457"
Verdict:ACCEPTED, Visibility:1, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -2", ExpOutput:"-1365
", Output:"-1365"
Verdict:ACCEPTED, Visibility:1, Input:"2 5
1 1", ExpOutput:"8
", Output:"8"
Verdict:ACCEPTED, Visibility:0, Input:"10 30
1 2 3 4 5 6 7 8 9 10", ExpOutput:"55312397
", Output:"55312397"
Verdict:ACCEPTED, Visibility:0, Input:"20 30
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1", ExpOutput:"-341
", Output:"-341"
*/
#include <stdio.h>
void read_into_array(int arr[],int size)
{
    int i;
    for(i=0;i<size;i++)
    {
        scanf("%d ",&arr[i]);
    }
}
void extension(int arr[],int size,int d)
{
     int i,j=d;
     while(j<=size)
     {
     arr[j]=0;
     for(i=1;i<=d;i++)
     {
         arr[j]+=arr[j-i];
     }
     j++;
     }
}

int main()
{
    int d,N,a[30];
    scanf("%d %d\n",&d,&N);
    read_into_array(a,d);
    extension(a,N,d);
    printf("%d",a[N]);
}