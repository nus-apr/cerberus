/*numPass=2, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"no"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:""
*/
#include <stdio.h>

int main() 
{
    int a[8][8],n,i,j;
    int r[8],c[8];
    
	scanf("%d",&n);
	
	if(n>=8)
	{
	    printf("no");
	    return 0;
	}
	
	for(i=0;i<n;i++)
	    scanf("%d %d",&r[i],&c[i]);
	
	for(i=0;i<n;i++)
	{
	    for(j=(i+1);j<n;j++)
	    {
	        if(r[i]==r[j])
	        {
	            printf("no");
	            return 0;
	        }
	    }
	}
	
	for(i=0;i<n;i++)
	{
	    for(j=(i+1);j<n;j++)
	    {
	        if(c[i]==c[j])
	        {
	            printf("no");
	            return 0;
	        }
	    }
	}
	    int p,q;
	 for(i=1;i<n;i++)
	 {
	     p=c[i]-r[i];
    	     for(j=(i+1);j<n;j++)
    	     {
    	       q=c[j]-r[j];  
    	       if(p==q||p==(-q))
    	       printf("no");
    	       return 0;
    	     }
	 }  
	 printf("yes");
	
	return 0;
}