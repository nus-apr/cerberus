/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 0 1
1 0 1 0
0 1 0 1
1 0 1 0 
2", ExpOutput:"1 2 1 2 ", Output:"1 2 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0 
3", ExpOutput:"1 2 3 2 ", Output:"1 2 3 2 "
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3", ExpOutput:"1 2 3 2 ", Output:"1 2 3 2 "
Verdict:ACCEPTED, Visibility:0, Input:"2
0 1
1 0
2", ExpOutput:"1 2 ", Output:"1 2 "
Verdict:ACCEPTED, Visibility:0, Input:"1
0
2", ExpOutput:"1 ", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"4 
0 1 1 1 
1 0 1 1 
1 1 0 1 
1 1 1 0
1000", ExpOutput:"1 2 3 4 ", Output:"1 2 3 4 "
*/
#include <stdio.h>
#include<stdlib.h>

void colour(int ** g,int c,int m,int *col)
{
    int i;
    col[0]=1;
    int* temp;
    for(i=1;i<c;i++)
    {
        temp=(int*)calloc(i,sizeof(int));
        int j;
        for(j=0;j<i;j++)
        {
            if(g[i][j]==1)
                temp[j]=col[j];
        }
        int counter=1;
        int l,flag=0;
        //while(flag!=j)
        for(counter=1;;counter++)
        {
            flag=0;
            for(l=0;l<j;l++)
            {
                if(counter!=temp[l])
                    flag++;
            }
            if(flag==j)
            break;
        }
        col[i]=counter;
    }
}
int main()
{
	int c,m,**g,*col;
	scanf("%d",&c);
	g=(int**)malloc(c*sizeof(int*));
	col=(int*)malloc(c*sizeof(int));
	int i,j;
	for(i=0;i<c;i++)
	    g[i]=(int*)malloc(c*sizeof(int));
	for(i=0;i<c;i++)
	{
	    for(j=0;j<c;j++)
	        scanf("%d",&g[i][j]);
	}
	//printf("%d",g[0][1]);
	scanf("%d",&m);
	colour(g,c,m,col);
	for(i=0;i<c;i++)
	    printf("%d ",col[i]);
	return 0;
}