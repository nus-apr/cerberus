/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"234"
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"145"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1412"
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12"
*/
#include<stdio.h>
#include<stdlib.h>
struct node{
    int data;
    int* next;
};

int main()
{
    struct node x,y;
    scanf("%d\n",&x.data);
    x.next=(int*)malloc(x.data*(sizeof(int)));
    for(int i=0;i<x.data;i++)
    {
        scanf("%d\n",&x.next[i]);
    }
    scanf("%d\n",&y.data);
    y.next=(int*)malloc(y.data*(sizeof(int)));
    for(int i=0;i<y.data;i++)
    {
        scanf("%d ",&y.next[i]);
    }
    for(int i=0;i<x.data;i++)
    {
        for(int j=0;j<y.data;j++)
        {
            if(x.next[i]==y.next[j])
            printf("%d",x.next[i]);
        }
    }
    return 0;
    
}