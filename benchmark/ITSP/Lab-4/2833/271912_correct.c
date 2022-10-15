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
    int n,c=0,x,y,z;
    scanf("%d",&n);
    for(x=1;x<=n;x=x+1){
     for(y=1;y<=x;y=y+1){
     for(z=1;z<=y;z=z+1){
          if(x+y>z && y+z>x && z+x>y)
     c++;
    }   
     }
    }
    printf("Number of possible triangles is %d",c);
    return 0;

}