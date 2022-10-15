/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"3
1 1
2 3
4 5", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 1
2 3
4 6
7 0", ExpOutput:"yes
", Output:"yes"
Verdict:ACCEPTED, Visibility:0, Input:"4
0 0
4 5
5 4
3 6", ExpOutput:"no
", Output:"no"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 2
5 4
4 7
0 0", ExpOutput:"yes
", Output:"yes"
*/
#include <stdio.h>
int check(int ,int[],int[] );
int flag=0;
int main() {
    int n,i;
    scanf("%d\n",&n);
    int r[n-1];
    int c[n-1];
	
	for(i=0;i<n;i++)  //filling the row and column
	{
	    scanf("%d %d\n",&r[i],&c[i]);
        
	    
	}
	flag=check(n,r,c);
	
	if(flag==1)
{
    printf("no");
    
}
else if (flag==0)
{
    printf("yes");
}	
	
	return 0;
}
int check(int n,int r[],int c[])
{
int i,j;
	for(i=0;i<n;i++)
	{
	    for(j=i+1;j<n;j++)
	    {
	        	if(r[i]==r[j])//rows are same
	        
	        {	flag=1;
	        		break;
	        }		
	        	else if(c[i]==c[j]) //columns are same
	        {
	        	flag=1;
	        		break;
	        }	
	        	else if(r[j]-r[i]==c[j]-c[i]) //right diagonal are same 
	        {	
	        	flag=1;
	        	    break;
	        }	    
	        	else if(r[i]+c[i]==r[j]+c[j]) //left diagonal are same
	        {	
	        	flag=1;
	        		break;
	        }		
	    }
	    if (flag==1)
	    break;
	    
	}
	    
	    return flag;
	}
