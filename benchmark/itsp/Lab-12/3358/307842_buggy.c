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
#include <stdio.h>
#include <stdlib.h>

struct set{
    int size;
    int* elt;
};

int main() {
    int a,b,i,j;
    scanf("%d",&a);
    struct set A,B;
    A.size=a;
    A.elt=(int*)(malloc(a*sizeof(int)));
    for(i=0;i<a;i++)
    {
        scanf ("%d",&A.elt[i]);
    }
    scanf("%d",&b);
    B.size=b;
    B.elt=(int*)(malloc(b*sizeof(int)));
    for(j=0;j<b;j++)
    {
        scanf("%d",&B.elt[j]);
    }
    for(i=0;i<a;i++)
    {
        for(j=0;j<b;j++)
        {
            if(A.elt[i]==B.elt[j])
            printf("%d",A.elt[i]);
        }
    }
    
    
    
    
    
    
    
    
    
    
    
    return 0;
}