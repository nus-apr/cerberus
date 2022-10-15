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
int max(int a,int b){
    return (a>b?a:b);
}
int max_sum(int num[],int i){//function to find largest element of an array
    int p=max(num[0],num[1]);
    for(int j=2;j<i;j++){
        p=max(p,num[j]);
    }
    return p;
}
int main() {
	int m,n,max;
	int mat[100][100];
	int rsum[100]={0};
	for(int i=0;i<100;i++){//initialising
	    for(int j=0;j<100;j++){//every element
	        mat[i][j]=0;//of mat[100][100] to 0
	    }
	}
	scanf("%d %d\n",&n,&m);
	for(int i=0;i<n;i++){
	    for(int j=0;j<m;j++){
	        scanf("%d ",&mat[i][j]);
	    }
	    scanf("\n");
	}
	for(int i=0;i<n;i++){
	    for(int j=0;j<m;j++){
	        rsum[i]=rsum[i]+mat[i][j];//finding sum of elements of row 
	    }
	}
	max=max_sum(rsum,n);
	for(int k=0;k<n;k++){
	    if(rsum[k]==max)//finding row of maximum sum
	        printf("%d ",k);
	}
	return 0;
}