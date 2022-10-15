/*numPass=1, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4", ExpOutput:"1 1 1 1 
2 1 1 
2 2 
3 1 
4 
", Output:"1 
1 
1 
1 
2 
1 
1 
2 
2 
3 
1 
4 
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5", ExpOutput:"1 1 1 1 1 
2 1 1 1 
2 2 1 
3 1 1 
3 2 
4 1 
5 
", Output:"1 
1 
1 
1 
1 
2 
1 
1 
1 
2 
2 
1 
3 
1 
1 
3 
2 
4 
1 
5 
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"2", ExpOutput:"1 1 
2 
", Output:"1 
1 
2 
"
Verdict:ACCEPTED, Visibility:1, Input:"1", ExpOutput:"1 
", Output:"1 
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6", ExpOutput:"1 1 1 1 1 1 
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
", Output:"1 
1 
1 
1 
1 
1 
2 
1 
1 
1 
1 
2 
2 
1 
1 
2 
2 
2 
3 
1 
1 
1 
3 
2 
1 
3 
3 
4 
1 
1 
4 
2 
5 
1 
6 
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"9", ExpOutput:"1 1 1 1 1 1 1 1 1 
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
", Output:"1 
1 
1 
1 
1 
1 
1 
1 
1 
2 
1 
1 
1 
1 
1 
1 
1 
2 
2 
1 
1 
1 
1 
1 
2 
2 
2 
1 
1 
1 
2 
2 
2 
2 
1 
3 
1 
1 
1 
1 
1 
1 
3 
2 
1 
1 
1 
1 
3 
2 
2 
1 
1 
3 
2 
2 
2 
3 
3 
1 
1 
1 
3 
3 
2 
1 
3 
3 
3 
4 
1 
1 
1 
1 
1 
4 
2 
1 
1 
1 
4 
2 
2 
1 
4 
3 
1 
1 
4 
3 
2 
4 
4 
1 
5 
1 
1 
1 
1 
5 
2 
1 
1 
5 
2 
2 
5 
3 
1 
5 
4 
6 
1 
1 
1 
6 
2 
1 
6 
3 
7 
1 
1 
7 
2 
8 
1 
9 
"
*/
#include <stdio.h>

void valid_seq(int a,int arr[],int sum,int check)
{
    if(sum==a)
    {
        for(int i=0;i<check;i++)
        {
            printf("%d \n",arr[i]);
        }
    
    return;    
    }
    int count=1;
    while(count<=(a-sum)&&(check==0||count<=arr[check-1]))
    {
        arr[check]=count;
        valid_seq(a,arr,sum+count,check+1);
        count++;
    }
} 
    void print_seq(int a)
    {
        int *arr;
        arr=(int*)malloc(a*sizeof(int));
        valid_seq(a,arr,0,0);
        
    }


int main(){
    int x;
    scanf("%d",&x);
    print_seq(x);
	return 0;
}