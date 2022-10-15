/*numPass=2, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
abcde
5
dceab", ExpOutput:"Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
xatps
5
sptay", ExpOutput:"Not Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmaex", ExpOutput:"Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
hello
5
lolhe", ExpOutput:"Valid", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5
hello
7
labexam", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:ACCEPTED, Visibility:0, Input:"7
anagram
6
anagrm", ExpOutput:"Not Valid", Output:"Not Valid"
Verdict:WRONG_ANSWER, Visibility:0, Input:"6
pppqqq
6
qpqpqp", ExpOutput:"Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abcdefg
7
gfedbac", ExpOutput:"Valid", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 
p
1 
p", ExpOutput:"Valid", Output:""
*/
#include <stdio.h>
#include <stdlib.h>
int valid(char * s1, char * s2, int n){
    int count;
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<n;j++)
        {
            if(s1[i]==s2[j])
            {
                count =1;
            }
        }
        if(count==1)
        {
            count =0;
        }
        else
        {
            printf("Not Valid");
            return 0;
        }
    }
    printf("Valid");
    return 1;
    
}

int main()
{

int m;
char *pow;
scanf("%d",&m); 
pow = (char *) malloc((m+1) * sizeof(char));
scanf("%s",pow);
int n;
char *pow2;
scanf("%d",&n); 
pow2 = (char *) malloc((n+1) * sizeof(char));
scanf("%s",pow2);
if (n==m)
{
    valid(*pow,*pow2,n);
}
else
{
    printf("Not Valid");
}

    //Fill this area with your code.
    return 0;
}