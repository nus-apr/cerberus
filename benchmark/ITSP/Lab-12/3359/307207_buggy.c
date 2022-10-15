/*numPass=1, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"6 5 4 3 2 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"9 6 4 3 2 1 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"6 5 4 3 2 1 -1 -2 -4 -6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"7 6 5 3 1 "
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
", Output:"93 69 54 49 43 34 29 28 23 21 12 2 "
*/
#include <stdio.h>
#include <stdlib.h>
struct set
{
    int n;
    int *p;
};

int main() {
    int i,j,c[100];
    struct set *st;
        st=(struct set*)malloc(2*sizeof(struct set));//dynamic memory  
    for(i=0;i<2;i++)
    {
    scanf("%d",&(st[i].n));
    st[i].p=(int*)malloc(st[i].n*sizeof(int));
    for(j=0;j<st[i].n;j++)
    scanf("%d",&(st[i].p[j]));
    }
    int k=0,z=0,x;
    for(i=0;i<st[0].n;i++)
    {
        x=1;
        for(j=0;j<st[1].n;j++)
        {
            if(st[0].p[i]==st[1].p[j])
            {
                x=0;
                break;
            }
        }
        if(x==1)
        {
        c[k]=st[0].p[i];
     // printf("%d ",c[k]);
        k++;
        }
    }
    for(i=k;i<k+st[1].n;i++)
    {
        c[i]=st[1].p[z];
        z++;
    }
    z=i;
    
  int min,t;
  min=c[0];
  for(i=0;i<z;i++)
  {
      for(j=i;j<z;j++)
      {
          if(c[i]<c[j])
          {
              t=c[i];
              c[i]=c[j];
              c[j]=t;
          }
      }
  }
  for(j=0;j<z;j++)
   {
       printf("%d ",c[j]);
   }
    return 0;
}