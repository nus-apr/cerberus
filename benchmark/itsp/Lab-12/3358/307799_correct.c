/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"2 3 4 "
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6 "
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"1 4 5 "
Verdict:ACCEPTED, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 4 12 "
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12 "
*/
#include<stdio.h>
#include<stdlib.h>
struct set
{
    int x;
    int *a;
};
int main()
{
    int n1,n2,*a1,*a2,i,j;
    struct set s1,s2;
    scanf("%d",&n1);
    a1=(int*)malloc(n1*sizeof(int));
    s1.x=n1;
    for(i=0;i<n1;i++)
    {
        scanf("%d",&a1[i]);
    }
    s1.a=a1;
    scanf("%d",&n2);
    s2.x=n2;
    a2=(int*)malloc(n2*sizeof(int));
    for(i=0;i<n2;i++)
    {
        scanf("%d",&a2[i]);
    }
    s2.a=a2;
    for(i=0;i<n1;i++)
    {
        for(j=0;j<n2;j++)
        {
            if((s1.a[i])==(s2.a[j]))
            printf("%d ",(s1.a[i]));
        }
    }
    return 0;
}