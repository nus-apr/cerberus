/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:"0 1 2 3 4 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:"0 "
Verdict:ACCEPTED, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:"0 1 2 "
*/
#include <stdio.h>

int main() {
	int M[100][100],n,m,i,j;
	scanf("%d %d",&n,&m);
	for(i=0;i<n;i++){
	    for(j=0;j<m;j++){
	        scanf("%d",&M[i][j]);
	    }
	}
	int sum[n];
	for(i=0;i<n;i++){
	    int x=0;
	    for(j=0;j<m;j++){
	        x=x+M[i][j];           //adding the values in each line
	        sum[i]=x;
	    }
	}
	int y=0,x=(-2147483648);
	for(i=0;i<n;i++){             //checking maximum value
	    if(sum[i]>x){
	        x=sum[i];
	    }
	}
	for(i=0;i<n;i++){
	    if(sum[i]==x){
	        printf("%d ",i); //printing line number(s) of maximum value
	    }
	}
	return 0;
}