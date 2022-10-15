/*numPass=2, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"yes"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"yes"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"yes"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"yes"
*/
#include <stdio.h>
int checkrow(int r,int c,int chess1[8][8]){
    int j;
    for(j=0;j<8;j++){
        if(j==c)
        continue;
        else{
            if(chess1[r][j]==1)
            return 1;
            
        }
    }
    return 0;
}
int checkcolumn(int r,int c,int chess1[8][8]){
    int i;
    for(i=0;i<8;i++){
        if(i==r)
        continue;
        else{
            if(chess1[i][c]==1)
            return 1;
        }
    }
    return 0;
}
int checkdiagonal(int r,int c,int chess1[8][8]){
    int i,j;
    j=c+1;
    for(i=r+1;i<8;i++){
        if(j<8){
        if (chess1[i][j]==1)
        return 1;}
        j++;
    }
    j=c-1;
    for(i=r+1;i<8;i++){
        if(j>=0){
        if(chess1[i][j]==1)
        return 1;}
        j--;
    }
    j=c-1;
    for(i=r-1;i>=0;i--){
        if(j>=0){
        if(chess1[i][j]==1)
        return 1;}
        j--;
    }
    j=c+1;
    for(i=r-1;i>=0;i--){
        if(j<8){
        if(chess1[i][j]==1)
        return 1;}
        j++;
    }
    return 0;
        
    
}

int main() {
	int chess[8][8];
	int i,j,N,R,C,count=0;
	for(i=0;i<8;i++){
	    for(j=0;j<8;j++){
	        chess[i][j]=0;
	    }
	}
	scanf("%d\n",&N);
	for(i=1;i<=N;i++){
	    scanf("%d%d\n",&R,&C);
	    chess[R][C]=1;
	    
	}
	for(i=0;i<8;i++){
	    for(j=0;j<8;j++){
	        if (chess[i][j]==1){
	            if(!(checkrow(i,j,chess) && checkcolumn(i,j,chess) && checkdiagonal(i,j,chess))){
	                count++;
	            }
	            
	            
	        }
	    }
	}
	if(count==N){
	    printf("yes");
	}
	else{
	    printf("no");
	}
	return 0;
}