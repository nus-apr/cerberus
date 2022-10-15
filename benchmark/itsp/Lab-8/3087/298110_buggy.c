/*numPass=7, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"2 1 3
", Output:"2 1 3"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 0 0 5
6 0 8 0 10
11 0 0 5 5
-1 2 3 4 5", ExpOutput:"3 2 2
", Output:"3 2 2"
Verdict:ACCEPTED, Visibility:1, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 1 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 4
0 0 0 0
0 0 0 0
0 0 0 0
0 0 0 0", ExpOutput:"0 -1 -1
", Output:"0 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"1 1 1"
Verdict:ACCEPTED, Visibility:0, Input:"10 10
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
0 1 0 0 0 0 0 0 0 0
0 0 1 0 0 0 0 0 0 0", ExpOutput:"3 8 1
", Output:"3 8 1"
Verdict:ACCEPTED, Visibility:0, Input:"4 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 1 1 1", ExpOutput:"3 1 1
", Output:"3 1 1"
*/
#include <stdio.h>
void read_into_matrix(int a[][10],int m,int n){
    for(int i=0;i<=m-1;i++){
        for(int j=0;j<=n-1;j++){
            scanf("%d",&a[i][j]);
        }
    }
}
int goodness(int a[][10],int i,int j,int n){
    int k,l=0;
    for(k=0;k<=n-1;k++){
        if(a[i+k][j+k]!=0){
        l++;
        }
    }
    for(int p=0;p<=n-1;p++){
        for(int q=0;q<=n-1;q++){
            if(p!=q&&a[i+p][j+q]==0){
            l++;
            }
        }
        
    }
    if(l==n*n)
        return 1;
        else
        return 0;
}
int min(int a,int b){
    if(a<b)
    return a;
    else 
    return b;
}
int max(int a,int b){
    return a+b-min(a,b);
}
int max_matrix(int a[][10],int m,int n){
    int maximum=a[0][0];
    for(int i=0;i<=m-1;i++){
        for(int j=0;j<=n-1;j++){
            maximum=max(maximum,a[i][j]);
        }
    }
    return maximum;
}
int main(){
    int a[10][10],m,n;
    int b[10][10];
    scanf("%d %d",&m,&n);
    read_into_matrix(a,m,n);
     for(int i=0;i<=m-1;i++){
      
        for(int j=0;j<=n-1;j++){
      
            
            if(a[i][j]==0){
                b[i][j]=0;
                
            }
            else{
            b[i][j]=1;
            int t=1;
            while(goodness(a,i,j,t)!=0)
            {
                t++;
            }
                
                b[i][j]=t-1;
                //break;
            }
            }
        }
    int bmax=max_matrix(b,m,n);
    printf("%d ",bmax);
    for(int i=0;i<=m-1;i++){
        for(int j=0;j<=n-1;j++){
            if(b[i][j]==bmax){
                printf("%d %d",i+1,j+1);
                goto end;
            }
        }
    }
    end:
    return 0;
}