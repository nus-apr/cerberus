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
int n;
int sum(int *arr,int top)
{
    int i,sum=0;
    for(i=0;i<=top;i++)
    sum+=arr[i];
    return sum;
}

void xyz(int *arr,int top)
{
    int i;
    int rsum=n-sum(arr,top);
    if(rsum==0)
    {
        for(i=0;i<=top;i++)
        printf("%d ",arr[i]);
        printf("\n");
       return;
    }
  for(i=1;i<=arr[top];i++)
  {
      if(rsum-i<0)
      break;
      else
      {
          arr[top+1]=i;
          xyz(arr,top+1);
      }
  }
}

int main(){
    scanf("%d",&n);
    int i,*arr;
    for(i=1;i<=n;i++)
    {
        arr=(int*)malloc((n+1-i)*sizeof(int));
        arr[0]=i;
        xyz(arr,0);
    }
	return 0;
}