/*numPass=3, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
34 13 42 14
2
13 42", ExpOutput:"YES
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"6
1 2 3 4 5 6
3
3 2 1", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 3 6 1
2
1 6", ExpOutput:"NO
", Output:"NO
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 3 5 7 9
2
2 4", ExpOutput:"NO
", Output:"NO
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
9 9 8 9 9
2
9 9", ExpOutput:"YES
", Output:"NO
"
*/
#include <stdio.h>
int check_arrays(int [],int [],int,int);//function to check contiguos                                            array
int main() {
	int s1,s2;
	int i;
    scanf("%d",&s1);
    int A1[s1];
    for(i=0;i<s1;i++)
    {
        scanf("%d",&A1[i]);
    }
    scanf("%d",&s2);
    int A2[s2];
    for(i=0;i<s2;i++)
    {
        scanf("%d",&A2[i]);
    }
   int ans=check_arrays(A1,A2,s1,s2);
   if(ans==1)
   {
       printf("YES\n");
   }
   else
   {
       printf("NO\n");
   }
	return 0;
}
int check_arrays(int B1[],int B2[],int c1,int c2)
{
    int i,c=0;
    for(i=0;i<c1-c2;i++)
    {
        if(B2[0]==B1[i])
        {
         c=1;
         break;
        }
    }
    if(c==0)
    return 0;
    int j=0;
    while(j<c2)
    {
        j++;
        i++;
        if((B2[j])!=B1[i])
        return 0;
    }
    return 1;
}