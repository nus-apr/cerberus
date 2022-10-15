/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4
34 13 42 14", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"4
11 2 18 2", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:1, Input:"8
1 21 34 45 53 65 71 8", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 2 3 4 1", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"6
1 2 3 4 5 6", ExpOutput:"NO
", Output:"NO"
*/
#include <stdio.h>
void read_into_array(int a[],int size)
{
    
    int i;
    for(i=0;i<size;i++)
    {
        scanf("%d", &a[i]);
    }
}
void equality(int b[],int N)
{
    
    int i,j,k=0;
    for(i=0; i<N; i++)
    {
        for(j=i+1;j<N;j++)
        {
            if(b[i]==b[j]&&i!=j)
            {
              k=1;
              printf("YES"); 
              break;
            }
            
        }
    }
    if(k==0)
    {
        printf("NO");
    }
}
int main() {
	int length;
	scanf("%d", &length);
	int s[length];
	read_into_array(s,length);
	equality(s,length);
	return 0;
}