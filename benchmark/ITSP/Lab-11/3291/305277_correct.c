/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4", ExpOutput:"1 1 1 1 
2 1 1 
2 2 
3 1 
4 
", Output:"1 1 1 1 
2 1 1 
2 2 
3 1 
4 
"
Verdict:ACCEPTED, Visibility:1, Input:"5", ExpOutput:"1 1 1 1 1 
2 1 1 1 
2 2 1 
3 1 1 
3 2 
4 1 
5 
", Output:"1 1 1 1 1 
2 1 1 1 
2 2 1 
3 1 1 
3 2 
4 1 
5 
"
Verdict:ACCEPTED, Visibility:1, Input:"2", ExpOutput:"1 1 
2 
", Output:"1 1 
2 
"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"1 
", Output:"1 
"
Verdict:ACCEPTED, Visibility:0, Input:"6", ExpOutput:"1 1 1 1 1 1 
2 1 1 1 1 
2 2 1 1 
2 2 2 
3 1 1 1 
3 2 1 
3 3 
4 1 1 
4 2 
5 1 
6 
", Output:"1 1 1 1 1 1 
2 1 1 1 1 
2 2 1 1 
2 2 2 
3 1 1 1 
3 2 1 
3 3 
4 1 1 
4 2 
5 1 
6 
"
Verdict:ACCEPTED, Visibility:0, Input:"9", ExpOutput:"1 1 1 1 1 1 1 1 1 
2 1 1 1 1 1 1 1 
2 2 1 1 1 1 1 
2 2 2 1 1 1 
2 2 2 2 1 
3 1 1 1 1 1 1 
3 2 1 1 1 1 
3 2 2 1 1 
3 2 2 2 
3 3 1 1 1 
3 3 2 1 
3 3 3 
4 1 1 1 1 1 
4 2 1 1 1 
4 2 2 1 
4 3 1 1 
4 3 2 
4 4 1 
5 1 1 1 1 
5 2 1 1 
5 2 2 
5 3 1 
5 4 
6 1 1 1 
6 2 1 
6 3 
7 1 1 
7 2 
8 1 
9 
", Output:"1 1 1 1 1 1 1 1 1 
2 1 1 1 1 1 1 1 
2 2 1 1 1 1 1 
2 2 2 1 1 1 
2 2 2 2 1 
3 1 1 1 1 1 1 
3 2 1 1 1 1 
3 2 2 1 1 
3 2 2 2 
3 3 1 1 1 
3 3 2 1 
3 3 3 
4 1 1 1 1 1 
4 2 1 1 1 
4 2 2 1 
4 3 1 1 
4 3 2 
4 4 1 
5 1 1 1 1 
5 2 1 1 
5 2 2 
5 3 1 
5 4 
6 1 1 1 
6 2 1 
6 3 
7 1 1 
7 2 
8 1 
9 
"
*/
#include <stdio.h>
#include<stdlib.h>

void print(int * t,int position,int sum,int n)
{
    
    if(sum>n)
    return;
    if(sum==n)
    {
        for(int i=0;i<position;i++)
        printf("%d ",t[i]);
        printf("\n");
        return ;
    }
    
    if(position!=0)
    {
        for(int i=1;i<=t[position-1];i++)
        {
            t[position]=i;
            print(t,position+1,sum+i,n);
        }
    }
    if(position==0)
    {
        for(int i=1;i<=n;i++)
        {
            t[position]=i;
            print(t,position+1,sum+i,n);
        }
    }
}
int main(){
    int n;
    scanf("%d",&n);
    
    int *arr;
    arr=(int*)malloc(n*sizeof(int));
    
    print(arr,0,0,n);
    
	return 0;

}
