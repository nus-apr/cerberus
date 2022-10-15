/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 13"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:ACCEPTED, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 7"
Verdict:ACCEPTED, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 22"
Verdict:ACCEPTED, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 50"
Verdict:ACCEPTED, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 3"
*/
#include<stdio.h>

int main()
{
int N;
scanf("%d",&N);
int a;
int b;
int c;
int x;
for(x=0,a=1;a<=N;a=a+1){
    for(b=1;b<=a;b=b+1){
        for(c=1;c<=b;c=c+1){
             if((a+b>c)&&(a+c>b)&&(b+c>a)){
         x=x+1;
             }
        }
        
    }
    
}

printf("Number of possible triangles is %d",x);
    
    return 0;
}