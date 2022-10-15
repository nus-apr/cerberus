/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 0 1
1 0 1 0
0 1 0 1
1 0 1 0 
2", ExpOutput:"1 2 1 2 ", Output:"1 2 1 2 "
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0 
3", ExpOutput:"1 2 3 2 ", Output:"1 2 3 2 "
Verdict:ACCEPTED, Visibility:1, Input:"4
0 1 1 1
1 0 1 0
1 1 0 1
1 0 1 0
3", ExpOutput:"1 2 3 2 ", Output:"1 2 3 2 "
Verdict:ACCEPTED, Visibility:0, Input:"2
0 1
1 0
2", ExpOutput:"1 2 ", Output:"1 2 "
Verdict:ACCEPTED, Visibility:0, Input:"1
0
2", ExpOutput:"1 ", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"4 
0 1 1 1 
1 0 1 1 
1 1 0 1 
1 1 1 0
1000", ExpOutput:"1 2 3 4 ", Output:"1 2 3 4 "
*/
#include <stdio.h>

int main(){
    int n,a,b;
    scanf("%d ",&n);
    int** ar=(int**)malloc(n*sizeof(int*));
    for(a=0;a<n;a++)
     *(ar+a)=(int*)malloc(n*sizeof(int));
    
    for(a=0;a<n;a++)
    {
        for(b=0;b<n;b++)
         scanf("%d ",(*(ar+a)+b));
    }
    /*for(a=0;a<n;a++)
    {
        for(b=0;b<n;b++)
         printf("%d ",*(*(ar+a)+b));
         printf("\n");
    }*/
    int cn=3;
    for(a=0;a<n;a++)
    {
        if((a==0)||(a==1))
        {
         printf("%d ",(a+1));
         continue;
        }
        int t=0;
        for(b=0;b<a;b++)
        {
            if((*(*(ar+a)+b))==0)
            {
                printf("%d ",b+1);
                t=1;
                break;
            }
        }
        if(t==1) continue;
        else
        {
            printf("%d ",cn++);
        }
    }
	return 0;
}