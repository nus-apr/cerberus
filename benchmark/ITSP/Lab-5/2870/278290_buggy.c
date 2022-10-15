/*numPass=6, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"14", ExpOutput:"17
", Output:"17"
Verdict:ACCEPTED, Visibility:1, Input:"24", ExpOutput:"29
", Output:"29"
Verdict:WRONG_ANSWER, Visibility:1, Input:"1", ExpOutput:"2
", Output:"1"
Verdict:ACCEPTED, Visibility:1, Input:"68", ExpOutput:"71
", Output:"71"
Verdict:ACCEPTED, Visibility:0, Input:"99", ExpOutput:"101
", Output:"101"
Verdict:ACCEPTED, Visibility:0, Input:"150", ExpOutput:"151
", Output:"151"
Verdict:ACCEPTED, Visibility:0, Input:"200", ExpOutput:"211
", Output:"211"
*/
#include<stdio.h>
int x,n,y;
    

int check_prime(int n){
        for(x=2;x<=n/2;x++){
            if(n%x==0){
            return 10;}
        }
        return 2;
    }       
    int main(){
    scanf("%d",&n);
    for(y=n;y>=n;y++){
        if (y==1){
            printf("%d",y);
            break;
        }
        if(check_prime(y)==2){
            printf("%d",y);
            break;
        }
            
        }
    
    
    
    //Write your code here
    
    return 0;
}