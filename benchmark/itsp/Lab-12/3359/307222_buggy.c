/*numPass=3, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 5 6 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"3 2 4 9 1 6 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"1 2 3 5 6 -6 -4 -2 -1 4 "
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"9 2 1 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"28 49 23 29 2 69 34 12 93 21 43 54 "
*/
#include <stdio.h>
#include <stdlib.h>

struct set
{
    int n;
    int* p;
};

void uni(int* p1,int n1,int* p2,int n2)
 {
    int i,j,count=0,*arr;
    
    for(i=0;i<n1;i++)
    {
        for(j=0;j<n2;j++)
        {
            if(*(p1+i)==*(p2+j))
            {
                *(p2+j)=0;
                count++;
                
            }
        }
    }
    arr=(int*)malloc((n1+n2-count)*sizeof(int));
    
    for(i=0;i<n1;i++)
    arr[i]=*(p1+i);
 
     
       for(j=0;j<n2;j++)
        if(*(p2+j)!=0)
         {
            arr[i]=(*(p2+j));
            i++;
         } 
         //printf("%d ",count);
         //sort(arr);
         for(i=0;i<(n1+n2-count);i++)
         printf("%d ",arr[i]);
 }
 
int main() {
  int i,j;
  
  struct set set1;
  struct set set2;
  
  scanf("%d",&set1.n);
  set1.p=(int*)malloc((set1.n)*sizeof(int));
  
  for(i=0;i<set1.n;i++)
  scanf("%d",&set1.p[i]);
  
  scanf("%d",&set2.n);
  set2.p=(int*)malloc((set2.n)*sizeof(int));
  
  for(i=0;i<set2.n;i++)
  scanf("%d",&set2.p[i]);
  
    uni(set1.p,set1.n,set2.p,set2.n);
    
    return 0;
}