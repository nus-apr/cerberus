/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2", ExpOutput:"47
55
56
", Output:"
47102158"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
11 2 18 2
2", ExpOutput:"13
20
20
", Output:"
133353"
Verdict:WRONG_ANSWER, Visibility:1, Input:"6
1 2 3 4 5 6
4", ExpOutput:"10
14
18
", Output:"
102442"
Verdict:WRONG_ANSWER, Visibility:0, Input:"8
2 4 6 8 10 11 12 14
6", ExpOutput:"41
51
61
", Output:"
4192153"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
2 4 -1 -5 2 5 6
4", ExpOutput:"0
0
1
8
", Output:"
0019"
*/
#include <stdio.h>

int main() 
{
    int N[20];
    int count=0,size,k,sum=0,j;
    scanf("%d\n",&size);
    if(size<=20)
        {
            while(count<size)
                {
                
                    scanf("%d", &N[count]);
           
                    count=count+1;
                }
            printf("\n");
            scanf("%d",&k);
            for(j=0;j<(size-(k-1));j++)
                {
                    for(count=j;count<k+j;count++)
                        {
                            sum=N[count] + sum;
                        }
                printf("%d" ,sum);
                }
        }
	return 0;
}