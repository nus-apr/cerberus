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
#include <stdio.h>
#include <stdlib.h>

struct Set
{
    int n;
    int *ar;
};
typedef struct Set set;
void init(set *a)
{
    scanf("%d",&(a->n));
    a->ar=(int *)calloc(a->n,sizeof(int));
    for(int i=0;i<(a->n);i++)
    {
        scanf("%d",&(a->ar[i]));
    }
}
int min(int a,int b)
{
    if(a<b)
        return a;
    else return b;
}
int intersection(set *a,set *b,int *ans)
{
    int k=0;
    for(int i=0;i<(a->n);i++)
    {
        for(int j=0;j<b->n;j++)
        {
            if(a->ar[i]==b->ar[j])
            {
                ans[k]=a->ar[i];
                k++;
            }
        }
    }
    return k;
}

void print(int ar[],int size){
    for(int i=0;i<size;i++){
        printf("%d ",ar[i]);
    }
}

int main()
{
    int size;
    set first,second;
    init(&first);
    init(&second);
    int *ans=(int *)calloc(min(first.n,second.n),sizeof(int));
    size=intersection(&first,&second,ans);
    print(ans,size);
    return 0;
}