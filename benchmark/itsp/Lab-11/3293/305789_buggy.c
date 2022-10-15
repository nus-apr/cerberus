/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 0 1
1 0 1 0
0 1 0 1
1 0 1 0 
2", ExpOutput:"1 2 1 2 ", Output:"1212"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0 
3", ExpOutput:"1 2 3 2 ", Output:"1232"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3", ExpOutput:"1 2 3 2 ", Output:"1232"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2
0 1
1 0
2", ExpOutput:"1 2 ", Output:"12"
Verdict:ACCEPTED, Visibility:0, Input:"1
0
2", ExpOutput:"1 ", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4 
0 1 1 1 
1 0 1 1 
1 1 0 1 
1 1 1 0
1000", ExpOutput:"1 2 3 4 ", Output:"1234"
*/
#include <stdio.h>

void check(int a[100][100], int j, int l[100]){
    int i,color=1;
    for(i=0;i<j;i++){
        if(a[j][i]==1){
            if(l[i]==color){
                color++;
            }
            else continue;
        }
        if(j==0){
            color=1;
            break;
        }
    }
    l[j]=color;
}

int main(){
    int country,matrix[100][100],i,j,code,l[100],color;
    scanf("%d",&country);
    for(i=0;i<country;i++){
        for(j=0;j<country;j++){
            scanf("%d",&matrix[i][j]);
        }
    }
    scanf("%d",&code);
    for(i=0;i<country;i++){
        check(matrix,i,l);
    }
    for(i=0;i<country;i++){
        printf(" %d",l[i]);
    }
    
	return 0;
}