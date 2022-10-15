/*numPass=4, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"2 3 4 
", Output:" 2  3  4 "
Verdict:ACCEPTED, Visibility:1, Input:"3
2 6 9
3 
4 6 8", ExpOutput:"6 
", Output:" 6 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 4 5 6 9
3
3 6 7", ExpOutput:"6 
", Output:" 6 "
Verdict:ACCEPTED, Visibility:0, Input:"3
1 4 5
3
3 6 7", ExpOutput:"
", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
1 4 5
3
1 4 5", ExpOutput:"1 4 5 
", Output:" 1  4  5 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 4 5 9 12
5
1 4 6 10 12", ExpOutput:"1 4 12 
", Output:" 1  4  12 "
Verdict:ACCEPTED, Visibility:0, Input:"3
5 9 12
5
1 4 6 10 12", ExpOutput:"12 
", Output:" 12 "
*/
#include<stdio.h>
struct set
{
     int size;
     int *p;
};
struct set set1,set2;
int main()
{int a[20],b[20],i,j;
    struct set  elements;
    scanf("%d",&set1.size);
    for(i=0;i<set1.size;i++)
    {
        scanf("%d",&a[i]);
    }
    scanf("%d",&set2.size);
    for(i=0;i<set2.size;i++)
    {
        scanf("%d",&b[i]);
    }
    for(i=0;i<set1.size;i++)
    {
       // printf(" %d",set2.size);
        for(j=0;j<set2.size;j++)
        {
           if(a[i]==b[j])
            printf(" %d ",a[i]);
        }
    }
    return 0;
}