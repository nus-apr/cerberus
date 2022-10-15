/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 13"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 7"
Verdict:ACCEPTED, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 22"
Verdict:ACCEPTED, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 50"
Verdict:ACCEPTED, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 3"
*/
#include<stdio.h>

int main(){
    int N,a,b,c,i;
    scanf("%d",&N);
    i=0;
    a=1;b=1;c=1;
   while(a<=N){
       b=1;
       while(b<=a){
           c=1;
            while(c<=b){
                if(a<c+b) i=i+1;
                
                c=c+1;
           }
            b=b+1;
       }
        a=a+1;
        
   }

/*Here, N-1 cases must be removed from i because in these cases, a>b+c. And, the number of possible triangles becomes i-(N-1)*/
    printf("Number of possible triangles is %d",i);

    return 0;
}