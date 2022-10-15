/*numPass=0, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:"2 3 4 4"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:"6 3"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:"6 5"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:"3"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:"1 4 5 3"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:"1 4 12 5"
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:"12 3"
*/
#include <stdio.h>
#include <stdlib.h>




int main()
{
    struct Set
{
    int n;
    int* p;
};
    struct Set set1;
    struct Set set2;
    int n1,n2;
    scanf("%d\n",&n1);
    set1.n=n1;
    set1.p=(int*)malloc(n1*sizeof(int));
    for(int i=0;i<n1;i++)
    {
        scanf("%d ",&(set1.p[i]));
    }
    scanf("%d\n",&n2);
    set2.n=n2;
    set2.p=(int*)malloc(n2*sizeof(int));
    for(int i=0;i<n2;i++)
    {
        scanf("%d ",&(set2.p[i]));
    }
    for(int i=0;i<n1;i++)
    {
        for(int j=0;j<n2;j++)
        {
            if(*(set1.p+i)==*(set2.p+j))
            {
                printf("%d ",*(set1.p+i));
            }
        }
    }
    printf("%d",set1.n);
    return 0;
}







