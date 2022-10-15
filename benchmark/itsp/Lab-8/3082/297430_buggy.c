/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 3
1 1 1
1 1 1
1 1 1", ExpOutput:"0 1 2 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4
1 2 3 4
10 20 17 15
-10 -19 -2 -1", ExpOutput:"1 
", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 5
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
", ExpOutput:"0 1 2 3 4 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3
-1 -2 -3
-4 -5 -6
-7 -8 -9", ExpOutput:"0 
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 
-1 -1 -1
-1 -1 -1
-1 -1 -1", ExpOutput:"0 1 2 
", Output:""
*/
#include <stdio.h>
int max(int a,int b){
    return (a>b?a:b);
}
int max_sum(int num[],int i){
    int p=max(num[0],num[1]);
    for(int j=2;j<i;j++){
        p=max(p,num[j]);
    }
    return p;
}
int main() {
	int m,n,rsum[100]={0},max,mat[100][100];
	scanf("%d %d\n",&n,&m);
	for(int i=0;i<n;i++){
	    for(int j=0;j<m;j++){
	        scanf("%d ",&mat[i][j]);
	    }
	    scanf("\n");
	}
	for(int i=0;(i>=n)&&(i<100);i++){
	    for(int j=0;(j>=m)&&(j<100);j++){
	        mat[i][j]=0;
	    }
	}
	for(int i=0;i<n;i++){
	    for(int j=0;j<m;j++){
	        rsum[i]=rsum[i]+mat[i][j];
	    }
	}
	max=max_sum(rsum[100],n);
	for(int k=0;k<n;k++){
	    if(rsum[k]==max)
	        printf("%d ",k);
	}
	return 0;
}