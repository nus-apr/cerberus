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
int check_diagonal(int t[][2],int n);
int main(){
    int N;
    scanf("%d",&N);
    int q[N][2];
    for(int i=0;i<N;i++){
        for(int j=0;j<2;j++){
            scanf("%d",&q[i][j]);
        }
    }
   /* for(int i=0;i<N;i++){
        for(int j=0;j<2;j++){
            printf("%d",q[i][j]);
        }
    }*/
    int i,j;
    for(i=0;i<N;i++){
        for(j=i+1;j<N;j++){
            if((q[i][0]==q[j][0])||(q[i][1]==q[j][1])){
                printf("no");
                return 0;
            }
        }
    }
    if(check_diagonal(q,N))printf("yes");
    else printf("no");
    return 0;
}
int check_diagonal(int t[][2],int n){
    for(int i=0;i<n;i++){
        for (int j=i+1;j<n;j++){
            if ((t[i][0]+t[i][1])==(t[j][0]+t[j][1])){
                return 0;
            }
        }
    }
    
    for(int i=0;i<n;i++){
        for (int j=i+1;j<n;j++){
            if ((t[i][0]-t[i][1])==(t[j][0]-t[j][1])){
                return 0;
            }
        }
    }

    return 1;
}