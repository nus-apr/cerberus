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


int mod(int n)
{
    return n<0?-n:n;
}


int issafe(int arr[][8],int a,int b)
{    
    int x=a;          //checks if positon(a,b) is safe
    int y=b;
    
    
    for(int i=0;i<8;i++)    //for same row
    {
      if(i==b)
      continue;
      
      if(arr[a][i]==1)
      return 0;
    }
    
    for(int j=0;j<8;j++)   //for same column
    {
        if(j==a)
        continue;
        
        if(arr[j][b]==1)
        return 0;
    }
    
   /* while((x<8)&&(y<8))   //different cases of diagnols
    {
        if(arr[++x][++y]==1)
        return 0;
    }
    x=a;
    y=b;
    
    while((x>=0)&&(y>=0))
    if(arr[--x][--y]==1)
    return 0;
    
    x=a;
    y=b;
    
    while((x<8)&&(y<8)&&(x>=0)&&(y>=0))
    if(arr[--x][++y]==1)
    return 0;
    
    x=a;
    y=b;
    
    while((x<8)&&(y<8)&&(x>=0)&&(y>=0))
    if(arr[++x][--y]==1)
    return 0;
*/
    for(int i=0;i<8;i++)
    for(int j=0;j<8;j++)
    {
        if((i==a)&&(j==b))
        continue;
        
        if(arr[i][j]==1)
        if(mod(i-a)==mod(j-b))
        return 0;
        
    }
    return 1 ;
}

int main()
{   
    int r,c;
    int flag=0;
	int chess[8][8];
	int n=0;
	for(int i=0;i<8;i++)
	  for(int j=0;j<8;j++)
	    chess[i][j]=0;
	    
	    
	scanf("%d\n",&n);
	
	for(int i=1;i<=n;i++)
	{   
	    
	    scanf("%d %d\n",&r,&c);
	    chess[r][c]=1;
	}
	

	for(int i=0;i<8;i++)
	{
	    for(int j=0;j<8;j++)
	    {
	        if(chess[i][j]==1)
	        {
	            if(issafe(chess,i,j)==0)
	            {
	             printf("no");
	             flag=1;
	             break;
	            }
	        }
	        
	    }
	    
	    if(flag==1)
	    break;
	    
	}
	
	if(flag==0)
	printf("yes");

     
	return 0;
}