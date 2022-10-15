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

int main() 
{   int n=0,a[50],out=0;
    scanf("%d",&n);
    for(int i=0;i<n;i++)
    {  scanf("%d",&a[i]);
    }
	for(int i=0;i<n;i++)
	    {for(int j=i+1;j<n;j++)
            {       if(j>n)
                    {break;}
                    if(a[i]==a[j])
                    {  
                        out=out+1;
                    }
            }
        }
    if(out>0)
    {   printf("YES");
    }
    else
    {   printf("NO");
    }
	
	return 0;
}