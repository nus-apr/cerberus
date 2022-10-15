/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12", ExpOutput:"1
2
4
3
", Output:"1
2
4
3
"
Verdict:ACCEPTED, Visibility:1, Input:"3
13745 30 59 50
12845 31 23 50
12424 31 23 40
", ExpOutput:"12845
13745
12424
", Output:"12845
13745
12424
"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 50 20 30
4 30 40 10
2 40 40 10
3 35 29 40", ExpOutput:"3
1
2
4
", Output:"3
1
2
4
"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"3
4
1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 50 50 30
2 20 30 50
3 80 50 66 
4 10 29 10
5 10 10 10", ExpOutput:"3
2
1
4
5
", Output:"3
2
1
4
5
"
*/
#include <stdio.h>
#include <stdlib.h>
typedef struct std
{
    int rn,m,p,c;
}std;
void scanit(std* s)
{
    scanf("%d %d %d %d",&(s->rn),&(s->p),&(s->c),&(s->m));
}
void swap(std *a,std *b)
{
    std c=*a;
    *a=*b;
    *b=c;
}
int main() {
    int n;
    scanf("%d",&n);
    std* s=(std*)calloc(n,sizeof(std));
    for(int i=0;i<n;i++) scanit(s+i);
    
    for(int i=0;i<n;i++)
    {
        int max=(s+i)->m;int indx=i;
        for(int j=i+1;j<n;j++)
        {
            if(((s+j)->m)>max)
            {
                indx=j;
                max=(s+j)->m;
            }
            else if(((s+j)->m)==max)
            {
                if(((s+j)->p)>((s+indx)->p)) indx=j;
                else if(((s+j)->p)==((s+indx)->p))
                {
                    if(((s+j)->c)>((s+indx)->p)) indx=j;
                }
            }
        }
        swap(s+i,s+indx);
    }
    for(int k=0;k<n;k++) printf("%d\n",(s+k)->rn);
    return 0;
}