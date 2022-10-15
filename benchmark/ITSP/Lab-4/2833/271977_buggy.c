/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"Number of possible triangles is 13", Output:"Number of possible triangles is 34"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"Number of possible triangles is 1", Output:"Number of possible triangles is 1"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3", ExpOutput:"Number of possible triangles is 7", Output:"Number of possible triangles is 15"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5", ExpOutput:"Number of possible triangles is 22", Output:"Number of possible triangles is 65"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7", ExpOutput:"Number of possible triangles is 50", Output:"Number of possible triangles is 175"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2", ExpOutput:"Number of possible triangles is 3", Output:"Number of possible triangles is 5"
*/
#include<stdio.h>

int main()
{int n,i,j,k,s=0;
scanf("%d",&n);
for (i=1;i<=n;i=i+1)
{
    for (j=1;j<=n;j=j+1)
    {
        for (k=1;k<=n;k=k+1)
        {if (i+j>k&&i+k>j&&j+k>i)
        {s=s+1;
            
        }
            
            
        }
        
    }
    
    
    
}
    printf("Number of possible triangles is %d",s); 
    return 0;
}