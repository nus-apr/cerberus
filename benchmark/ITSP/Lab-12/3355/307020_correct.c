/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 6", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"4 10
-1 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"10 20
20 50", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"0 0
-1 0", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"-1 -5
-6 9", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"0 1
1 10", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"7 9
2 3", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"1 10
5 7", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"8 10
5 7", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
#include <stdlib.h>

typedef struct interval  //structure
{
    int li,ri;
} inv;
void inp_inv(inv* s)
{
    scanf("%d%d",&(s->li),&(s->ri));
}

void overlap(inv*,inv*); 

int main() {
    inv *A,*B;
    A=(inv*)malloc(sizeof(inv));
    B=(inv*)malloc(sizeof(inv));
    inp_inv(A); //inputting the values of the structure.
    inp_inv(B);
    overlap(A,B);
    return 0;
}

void overlap (inv* i1,inv* i2)
{
    if(((i1->li>=i2->li)&&(i1->li<=i2->ri))||((i1->ri>=i2->li)&&(i1->ri<=i2->ri))) //condition for overlap.
     printf("YES");
    else if((i1->li<=i2->li)&&(i1->ri>=i2->ri)) 
     printf("YES");
    else if((i2->li<=i1->li)&&(i2->ri>=i1->ri)) 
     printf("YES"); 
    else
     printf("NO");
}