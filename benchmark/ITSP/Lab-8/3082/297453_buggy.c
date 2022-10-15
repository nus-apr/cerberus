/*numPass=2, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"012"
Verdict:ACCEPTED, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"01234"
Verdict:ACCEPTED, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"012"
*/
#include <stdio.h>
int max(int a,int b){
    if(a>b)
    return a;
    else if(a<b)
    return b;
    else if(a==b)
    return a;
}
int main() {
	int n,m,i,j;
	int r[100];
	int mat[100][100];
	scanf("%d %d",&n,&m);
	for(i=0;i<n;i++){
	    r[i]=0;
	    for(j=0;j<m;j++){
	        scanf("%d",&mat[i][j]);
	        r[i]=r[i]+mat[i][j];
	    }
	}
	
	int s=r[0];
	for(i=0;i<n;i++){
	    if(r[i]>s)
	    s=r[i];
		    
	}
	for(i=0;i<n;i++){
	    if(r[i]==s)
	    printf("%d",i);
	}
	return 0;
}