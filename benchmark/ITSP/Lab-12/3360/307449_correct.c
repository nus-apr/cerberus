/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12", ExpOutput:"1
2
4
3
", Output:"1
2
4
3
"
Verdict:ACCEPTED, Visibility:1, Input:"3
13745 30 59 50
12845 31 23 50
12424 31 23 40
", ExpOutput:"12845
13745
12424
", Output:"12845
13745
12424
"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 50 20 30
4 30 40 10
2 40 40 10
3 35 29 40", ExpOutput:"3
1
2
4
", Output:"3
1
2
4
"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"3
4
1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 50 50 30
2 20 30 50
3 80 50 66 
4 10 29 10
5 10 10 10", ExpOutput:"3
2
1
4
5
", Output:"3
2
1
4
5
"
*/
#include <stdio.h>
#include <stdlib.h>

struct marks
{               //struct storing marks of a student
    int r;
    int p;
    int c;
    int m;
};

void swap(struct marks *a, struct marks *b)
{
    struct marks *tmp;
    tmp=(struct marks*)malloc(sizeof(struct marks));
    (*tmp).r=(*a).r;
    (*tmp).p=(*a).p;
    (*tmp).c=(*a).c;
    (*tmp).m=(*a).m;
    (*a).r=(*b).r;
    (*a).p=(*b).p;
    (*a).c=(*b).c;
    (*a).m=(*b).m;
    (*b).r=(*tmp).r;
    (*b).p=(*tmp).p;
    (*b).c=(*tmp).c;
    (*b).m=(*tmp).m;
 /*   *tmp=*a;
    *a=*b;
    *b=*tmp;*/
}

int main() 
{
    int n, i, j;//declaring variables
    struct marks tmp;
    struct marks *a;
                //pointer to structures
    scanf ("%d", &n);
                //scanning input
    a=(struct marks*)malloc(n*sizeof(struct marks));
                //dynamic memory allocation
    for(i=0; i<n; i++)
       scanf("%d %d %d %d",&((*(a+i)).r), &((*(a+i)).p), &((*(a+i)).c),                            &((*(a+i)).m));
    for (i=n-1; i>=0; i--)
    {           //sorting the structures
        struct marks *max;
        max=&a[0];
        for (j=1; j<=i; j++)
        {
            if (a[j].m>(*max).m)
                max=&a[j];
                //comparing marks in math
            else if (a[j].m==(*max).m)
            {   //if marks in maths are same compare phy score
            
                if (a[j].p>(*max).p)
                
                    max=&a[j];
                else if (a[j].p==(*max).p)
                {
                    if (a[j].c>(*max).c)
                    
                        max=&a[j];
                }
            }
        }
        swap(max, &a[i]);
        
    }
    for (i=n-1; i>=0; i--)
        printf ("%d\n", (a[i]).r);
                //printing reqd output
    free(a);    //erasing all
    return 0;
}