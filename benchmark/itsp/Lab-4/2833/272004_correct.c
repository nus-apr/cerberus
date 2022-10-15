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
    int N,i,j,k,x,y,m;
    x=0;N=0;y=0;m=0;
    i=1;
    scanf("%d",&N);
    for(i=1;i<=N;i++)
    {
      for(j=1;j<=N;j++)
      {
        for(k=1;k<=N;k++)
        {
            if((i+j>k)&&(i+k>j)&&(j+k>i))
            {
                x++;
            if(((i==j)&&j!=k)||((i==k)&&k!=j)||((j==k)&&k!=i))
            y++;
            
            if((i!=j)&&(j!=k)&&(k!=i))
            m++;
            }
        } 
      }
    }
    
    printf("Number of possible triangles is %d",x-y+(y/3)-m+(m/6));
    return 0;
}