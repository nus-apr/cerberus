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
int main(){
	int C,**G,m,i,j;
	scanf("%d\n",&C);
	G=(int**)malloc(sizeof(int*)*C);
	 for(i=0;i<C;i++)
	 G[i]=(int*)malloc(sizeof(int)*C);
	for(i=0;i<C;i++)
	{
	    for(j=0;j<C;j++)
	    {
	        scanf("%d ",&G[i][j]);
	    }
	    scanf("\n");
	}
	scanf("%d",&m);
	int *color;
	color=(int*)malloc(sizeof(int)*C);
	color[0]=1;
	for(i=1;i<C;i++)
	{  
	    for(j=0;j<i;j++)
	    {
	        if(G[i][j]==1)
	          color[i]=(color[i-1]<m?color[i-1]+1:color[i-1]-1);
	    }
	}
	for(i=0;i<C;i++)
	 printf("%d ",color[i]);
	return 0;
}