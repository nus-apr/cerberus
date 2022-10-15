/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"1 2 3 4 6 9 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"-6 -4 -2 -1 1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"1 3 5 6 7 "
Verdict:ACCEPTED, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 2 9 "
Verdict:ACCEPTED, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"2 12 21 23 28 29 34 43 49 54 69 93 "
*/
#include <stdio.h>
#include <stdlib.h>
struct set{
    int n;
    int* elements;
};
void read_to_struct(struct set* a)
{
    scanf("%d",&(a->n));
    int b=a->n;
    (a->elements)=(int*)malloc(sizeof(int)*b);
    for(int i=0;i<b;i++)
    {
        scanf("%d",(a->elements)+i);
    }
}
int selection_sort(int* a,int n)
{
    if(n==1)
        return 0;
    int i,max,maxi,temp;
    max=a[0];
    maxi=0;
    for(i=0;i<n;i++)
    {
        temp=a[i];
        if(temp<max)
        {
            max=temp;
            maxi=i;
        }
    }
    a[maxi]=a[0];
    a[0]=max;
    selection_sort(a+1,n-1);
}
void union_set(struct set* a,struct set* b)
{
    int i=0,j=0,temp1,temp2;
    while(i<a->n && j<b->n)
    {
        temp1=*(a->elements+i);
        temp2=*(b->elements+j);
        if(temp1>temp2)
        {
            printf("%d ",temp2);
            j++;
        }
        else if(temp2>temp1)
        {
            printf("%d ",temp1);
            i++;
        }
        else
        {
            printf("%d ",temp2);
            i++;
            j++;
        }
        
    }
    if(i==a->n)
    {
       for(int x=j;x<b->n;x++)
       {
            printf("%d ",*(b->elements+x));
       }
    }
    if(j==b->n)
    {
       for(int x=i;x<a->n;x++)
       {
            printf("%d ",*(a->elements+x));
       }
    }
    
}
int main() {
    struct set set1,set2;
    read_to_struct(&set1);
    read_to_struct(&set2);
    selection_sort(set1.elements,set1.n);
    selection_sort(set2.elements,set2.n);
    union_set(&set1,&set2);
    return 0;
}