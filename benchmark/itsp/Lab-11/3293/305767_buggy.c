/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 0 1
1 0 1 0
0 1 0 1
1 0 1 0 
2", ExpOutput:"1 2 1 2 ", Output:"1212"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0 
3", ExpOutput:"1 2 3 2 ", Output:"1232"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3", ExpOutput:"1 2 3 2 ", Output:"1232"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2
0 1
1 0
2", ExpOutput:"1 2 ", Output:"12"
Verdict:ACCEPTED, Visibility:0, Input:"1
0
2", ExpOutput:"1 ", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4 
0 1 1 1 
1 0 1 1 
1 1 0 1 
1 1 1 0
1000", ExpOutput:"1 2 3 4 ", Output:"1234"
*/
#include <stdio.h>
#include<stdlib.h>
int i[100],j[100],n=0;
void find0(int **arr,int m)
{
    for(int a=0;a<m;a++)
    {
        for(int b=0;b<a;b++)
        {
            if(arr[a][b]==0)
            {
                i[n]=a;
                j[n]=b;
                n++;
            }
        }
    }
    return;
}
int main(){
    int c,*arr,**g,m;
    scanf("%d",&c);
    arr=(int *)malloc(c*sizeof(int));
     g=(int **)malloc(c*sizeof(int*));
     for(int i=0;i<c;i++)
     {
         g[i]=(int *)malloc(c*sizeof(int));
     }
    for(int i=0;i<c;i++)
    {
        for(int j=0;j<c;j++)
        {
            scanf("%d",&g[i][j]);
        }
    }
    scanf("%d",&m);
    find0(g,c);
    for(int i=0;i<c;i++)
    {
        arr[i]=i+1;
    }
    for(int p=0;p<n;p++)
    {
        arr[j[p]]=j[p]+1;
        arr[i[p]]=j[p]+1;
    }
    for(int i=0;i<c;i++)
    {
        printf("%d",arr[i]);
    }
	return 0;
}