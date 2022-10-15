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
", Output:"no"
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
", Output:"no"
*/
#include <stdio.h>

int flag=0;
int main() {
    int n,a,b,i,j;
    int r[8];
    int c[8];
	scanf("%d\n",&n);
	for(i=0;i<8;i++)  //filling the row and column
	{
	    scanf("%d %d\n",&r[i],&c[i]);
        
	    
	}
	for(i=0;i<8;i++)
	{
	    for(j=i+1;j<8;j++)
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