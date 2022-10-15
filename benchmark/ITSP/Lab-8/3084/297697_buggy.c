/*numPass=3, numTotal=4
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
int safe(int mat[8][8],int i,int j){
    int k,l,check=1;
    k=i;
    l=j;
    for(j=0;j<8;++j){
        if(j==l){
                continue;
            }
        else if(mat[i][j]!=0){
                check=0;
                break;
            }
        }
    if(check==1){
        j=l;
        for(i=0;i<8;++i){
            if(i==k){
                continue;
                }
            else if(mat[i][j]!=0){
                check=0;
                break;
                }
            }
        }
    if(check==1){
        i=k;
        j=l;
        if(j>i){
            for((i=0,j=l-k);j<8;(++i,++j)){
                if((i==k)||(j==l)){
                    continue;
                }
                else if(mat[i][j]!=0){
                    check=0;
                    break;
                    }
                }
            }
        else{
            for((j=0,i=k-l);i<8;(++i,++j)){
                if((i==k)||(j==l)){
                    continue;
                }
                else if(mat[i][j]!=0){
                    check=0;
                    break;
                    }
                }
            }
        }
    if(check==1){
        i=k;
        j=l;
        if(i+j<7){
            for((j=0,i=(k+l));i>0;(++j,--i)){
                if((j==l)||(i==k)){
                    continue;
                }
                else if(mat[i][j]!=0){
                    check=0;
                    break;
                }
            }
        }
        else{
            for((i=7,j=(k+l-7));j<8;(++j,--k)){
                if((j==l)||(i==k)){
                    continue;
                }
                else if(mat[i][j]!=0){
                    check=0;
                    break;
                }
            }
        }
    }
    return check;
}


int main() {
	int n,i,j,mat[8][8],check=1,k,count=0;
	for(i=0;i<8;++i){
	    for(j=0;j<8;++j){
	        mat[i][j]=0;
	    }
	}
	scanf("%d",&n);
	for(k=0;k<n;++k){
	    scanf("%d%d",&i,&j);
	    mat[i][j]=1;
	}
    for(i=0;i<8;++i){
        for(j=0;j<8;++j){
            if(mat[i][j]!=0){
                check=safe(mat,i,j);
                if(check==1){
                    count++;
                    continue;
                }
                else{
                    printf("no");
                    return 0;
                }
            }
        }
    }
    if(count==n){
        printf("yes");
    }
	return 0;
}