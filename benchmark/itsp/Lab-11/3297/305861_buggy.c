/*numPass=2, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 3 4 5", ExpOutput:"1 2 3 4 5 
", Output:"2 3 4 5 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
5 4 3 2 1", ExpOutput:"1 2 3 4 5 
", Output:"5 5 5 5 5 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 3 2 1", ExpOutput:"1 1 2 3 
", Output:"3 3 3 3 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 4 3 2 1 0", ExpOutput:"0 1 1 2 3 4 
", Output:"4 4 4 4 4 4 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"10
1 4 3 2 1 0 5 8 100 110", ExpOutput:"0 1 1 2 3 4 5 8 100 110 
", Output:"4 4 4 4 4 5 8 100 110 110 "
Verdict:ACCEPTED, Visibility:0, Input:"0", ExpOutput:"
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1
42", ExpOutput:"42 
", Output:"42 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"11
1 4 3 2 1 0 5 8 100 110 -10", ExpOutput:"-10 0 1 1 2 3 4 5 8 100 110 
", Output:"4 4 4 4 4 4 5 8 100 110 110 "
*/
#include <stdio.h>
void swap(int *m,int *n)
{
    int t=*m;
    *m=*n;
    *n=t;
}
void sort(int *x,int y)
{
    int i,j,a,b,c;
    for(i=1;i<y;i++)
    {

            a=*(x+i);
            for(j=(i-1);j>=0;j--)
            {
                if(a<*(x+j))
                *(x+j+1)=*(x+j);
                else
                break;
            }
            *(x+j)=a;

    }
    for(i=0;i<y;i++)
    printf("%d ",*(x+i));
}
int main()
{
    int *a,b,i;
    scanf("%d",&b);
    a=(int*)malloc(b*sizeof(int*));
    for(i=0;i<b;i++)
    scanf("%d",(a+i));
    sort(a,b);
	return 0;
}