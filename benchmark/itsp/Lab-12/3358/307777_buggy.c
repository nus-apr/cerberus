/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"234"
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"145"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1412"
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12"
*/
#include<stdio.h>
#include<stdlib.h>
int main()
{  
    struct data
    {
        int n;
        int*a;
    };
    struct data x,y;
    scanf("%d",&x.n);
    x.a=(int*)malloc(x.n*sizeof(int));
    for(int i=0;i<x.n;i++)
    {
        scanf("%d",&x.a[i]);
    }
    scanf("%d",&y.n);
    y.a=(int*)malloc(y.n*sizeof(int));
    for(int i=0;i<y.n;i++)
    {
        scanf("%d",&y.a[i]);
    }
    for(int i=0;i<x.n;i++)
    {
        for(int j=0;j<y.n;j++)
        {
            if(x.a[i]==y.a[j])
            printf("%d",x.a[i]);
        }
    }
}