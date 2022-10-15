/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"1111
1  1
1  1
1  1
1111"
Verdict:ACCEPTED, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"22222
2   2
2   2
2   2
2   2
22222"
Verdict:ACCEPTED, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"999999
9    9
9    9
9    9
9    9
9    9
999999"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"3333
3  3
3  3
3  3
3333"
Verdict:ACCEPTED, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22
22"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"333
3 3
333"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"11
"
*/
#include <stdio.h>

int main(){
    int N,w,h;
    scanf("%d%d%d",&N,&w,&h);
    
    if(h>=2&&w>=2){
    int i,j,k;
    for(i=1;i<=w;i++){
        printf("%d",N);
    }
    printf("\n");
    for(j=1;j<=(h-2);j++){
        printf("%d",N);
            for(k=1;k<=(w-2);k++){
                printf(" ");
            }    
        printf("%d\n",N);
        
    }
     for(i=1;i<=w;i++){
        printf("%d",N);
     }}
    int l,m;
    if(h==1){
        for(l=1;l<=w;l++){
            printf("%d",N);
        }
    }
    if(w==1){
        for(m=1;m<=h;m++){
            printf("%d\n",N);
        }
    }
    
    return 0;
}