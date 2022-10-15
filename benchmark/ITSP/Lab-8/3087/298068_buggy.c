/*numPass=7, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"2 1 3
", Output:"2 1 3"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 0 0 5
6 0 8 0 10
11 0 0 5 5
-1 2 3 4 5", ExpOutput:"3 2 2
", Output:"3 2 2"
Verdict:ACCEPTED, Visibility:1, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"4 4
0 0 0 0
0 0 0 0
0 0 0 0
0 0 0 0", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:0, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:0, Input:"10 10
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
0 1 0 0 0 0 0 0 0 0
0 0 1 0 0 0 0 0 0 0", ExpOutput:"3 8 1
", Output:"3 8 1"
Verdict:ACCEPTED, Visibility:0, Input:"4 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 1 1 1", ExpOutput:"3 1 1
", Output:"3 1 1"
*/
#include <stdio.h>
int max(int a,int b)
{
    if(a>b)
        return a;
    else return b;
}
void inar(int ar[][100],int r,int c)
{
    int i=0,j=0;
    for(;i<r;i++)
        for(j=0;j<c;j++)
            scanf("%d",&ar[i][j]);
}
int good(int ar[][100],int r,int c);
int check(int ar[][100],int r,int c,int pos1,int pos2);
int main()
{
    int ar[100][100];
    int r,c;
    scanf("%d%d",&r,&c);
    inar(ar,r,c);
    good(ar,r,c);
    return 0;
}

int good(int ar[][100],int r,int c)
{
    int i=0,j=0,goodness=0,pos1=-1,pos2=-1,ans=0;
    for(;i<r;i++)
    {
        for(j=0;j<c;j++)
        {
            if(ar[i][j]!=0)
            {
                goodness=check(ar,r,c,i,j);
                if(goodness>ans)
                {
                    pos1=i;
                    pos2=j;
                    ans=goodness;
                }
            }
        }
    }
    if(ans==0)
        printf("%d %d %d",0,-1,-1);
    else
        printf("%d %d %d",ans,pos1+1,pos2+1);
    return ans;
}

int check(int ar[][100],int r,int c,int pos1,int pos2)
{
    int i=0,j=0,size=0;
    for(i=0;(i+pos1<r)&&(i+pos2<c);i++)
    {
        if(ar[i+pos1][i+pos2]==0)
            break;
    }
    if(i==1)
        return 0;
    size=i;
    for(i=0;i<size;i++)
    {
        for(j=0;j<size;j++)
        {
            if(i!=j)
            {
                if(ar[i+pos1][j+pos2]!=0)
                {
                    size=max(i,j);
                }
            }
        }
    }
    if(size==1&&size==0)
        return 0;
    else return size;
}