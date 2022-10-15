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
void clrcntry(int **g,int c,int m){
    printf("1 ");
    for(int i=1;i<c;i++){
        for(int j=0;j<c;j++){
            if(g[i][j]==0){
                printf("%d ",j+1);
                break;    
            }
        }
    }
}
int main(){
	int **g,c,m;
	scanf("%d",&c);
	g=(int **)malloc(c*sizeof(int *));
	for(int i=0;i<c;i++)
	    g[i]=(int *)malloc(c*sizeof(int));
	    
	for(int i=0;i<c;i++){
	    for(int j=0;j<c;j++){
	        scanf("%d ",&g[i][j]);
	    }
	    scanf("\n");
	}
   /* for(int i=0;i<c;i++){
	    for(int j=0;j<c;j++){
	        printf("%d ",g[i][j]);
	    }
	    printf("\n");
	}*/
	scanf("%d",&m);
	clrcntry(g,c,m);
	return 0;
}