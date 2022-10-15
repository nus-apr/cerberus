/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"234"
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"145"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1412"
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12"
*/
#include <stdio.h>


struct pt{
    int n;
    int *arr;
    
}; 

int main(){
    int i;
    struct pt pt1;
    struct pt pt2;
    pt1.arr = (int *)malloc((pt1.n)*sizeof(int));
    pt2.arr = (int *)malloc((pt2.n)*sizeof(int));
    scanf("%d",&pt1.n);
    for(i=0;i<pt1.n;i++){
        scanf("%d",&pt1.arr[i]);
    }
    scanf("%d",&pt2.n);
    for(i=0;i<pt2.n;i++){
        scanf("%d",&pt2.arr[i]);
    }
    int j;
    int x = 0;
    int *ans;
    ans = (int *)malloc((pt1.n+pt2.n)*sizeof(int));
    for(i=0;i<pt1.n;i++){
        for(j=0;j<pt2.n;j++){
            if(pt1.arr[i]==pt2.arr[j]){
               ans[x]=pt1.arr[i];
               x++;
               break;
            }
            
        }
        
        
    }
    for(i=0;i<x;i++){
        printf("%d",ans[i]);
    }
    
    
    
    
    
    
    return 0;
}