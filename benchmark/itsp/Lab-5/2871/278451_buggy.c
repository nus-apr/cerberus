/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"11 1 1 111   11   11   111 1 1 11"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"22 2 2 2 222    22    22    22    222 2 2 2 22"
Verdict:WRONG_ANSWER, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"99 9 9 9 9 999     99     99     99     99     999 9 9 9 9 99"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"33 3 3 333   33   33   333 3 3 33"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22 2222 22"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"33 3 333  333 3 33"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1111"
*/
#include<stdio.h>

int main(){
	int N,w,h,i,j;
	scanf("%d %d %d",&N,&w,&h);
	for(i=1;i<=h;i++){
	    for(j=1;j<=w;j++){
	        if(i==1){
	            printf("%d",N);
	        }
	        if(i==h){
	            printf("%d",N);
	        }
	        if(j==1){
	            printf("%d",N);
	        }
	        if(j==w){	            
	            printf("%d",N);
	        }
	        else {
	            printf(" ");
	        }
	       	}
	    
	}
	
	return 0;
}