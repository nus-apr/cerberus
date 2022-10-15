/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"no"
*/
#include <stdio.h>

int main() {
	int n,r,c,i=0,j,x,m,z=0;
	scanf("%d",&n);
	int mt[n][2];
	for(i=0;i<3;i++){
	    for(j=0;j<2;j++){
	        scanf("%d",&mt[i][j]);
	    }
	}
	for(i=0;i<n;i++){
	    for(m=1;m<n-1;m++){
	        x=mt[i][0]-mt[i+m][0];
	        if(x==0){
	            z=1;
	        }
	        else if((mt[i][1]-mt[i+m][1]==x)||(mt[i][1]-mt[i+m][1]==-x)||(mt[i][1]-mt[i+m][1]==0)){
	            z=1;
	        }
	    }
	}
	if(z==1){
	    printf("yes");
	}
	else printf("no");
	return 0;
}