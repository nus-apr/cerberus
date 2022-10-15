/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"yes"
Verdict:ACCEPTED, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"yes"
*/
#include <stdio.h>

int main() {
	int N,i,j,k=0,l=0,m;
	scanf("%d",&N);
	int pos[N][2];
	for(i=0;i<N;i++){
	    for(j=0;j<2;j++){
	        scanf("%d",&pos[i][j]);
	    }
	}
	for(i=0;i<N-1;i++){
	    for(j=i+1;j<N;j++){
	   if(*(*(pos+i)+0)==*(*(pos+j)+0)||*(*(pos+i)+1)==*(*(pos+j)+1)){
	       k=1;break;
	   } 
	    }
	}//printf("%d",k);
	for(i=0;i<N-1;i++){
	    for(j=i+1;j<=8;j++){
	        for(m=0;m<8;m++){
	        if(pos[i][0]+m==pos[j][0]&&pos[i][1]+m==pos[j][1]){
	            l=1;break;
	        }
	    }
	    }
	}//printf("%d",l);
	
	if(k==1||l==1){
	    printf("no");
	}
	else printf("yes");
	return 0;
}