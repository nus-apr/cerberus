/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
abc
4
dbca", ExpOutput:"1", Output:"
dbca3"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
abce
4
dbca", ExpOutput:"2", Output:"
dbca2"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
4
dbca", ExpOutput:"7", Output:"
dbca7"
Verdict:WRONG_ANSWER, Visibility:1, Input:"7
labexam
7
balmmmm", ExpOutput:"6", Output:"
balmmmm6"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
7
balmaex", ExpOutput:"0", Output:"
balmaex2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
balmaexam", ExpOutput:"2", Output:"
balmaexam2"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam
9
pqrstuvwp", ExpOutput:"16", Output:"
pqrstuvwp14"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
hellohi
9
lhoeidear", ExpOutput:"6", Output:"
lhoeidear6"
*/
#include <stdio.h>
#include <stdlib.h>

int makeEqual(char * s1, int n1, char * s2, int n2)
{
    int *a;
    a=(int *)malloc(256*sizeof(int));//creating array (ascii counter)
    for(int i=0;i<256;i++)
    {
        *(a+i)=0;//initialising by 0
    }    
    for(int i=0;i<n1;i++)
    {
        int d=*(s1+i);
        (*(a+d))++;//reporting if char is present in d1
    }
    for(int i=0;i<n2;i++)
    {
        int d=*(s2+i);//checking if char is also in s2
        (*(a+d))--;
    }
    int sum=0;
    for(int i=0;i<256;i++)
    {
        if(*(a+i)>0)
        sum=sum+(*(a+i));//checking how many char are different
        else
        sum=sum-(*(a+i));
    }
    return sum;
}

int main()
{
    int n1,n2;//declaration
    char *s1,*s2;
    scanf("%d",&n1);//input
    s1=(char *)malloc((n1+1)*sizeof(char));//dynamic allocation
    for(int i=0;i<=n1;i++)
    {
        scanf("%c",s1+i);//input
    }
    scanf("%d",&n2);//input
    s2=(char *)malloc((n2+1)*sizeof(char));//dynamic allocation
    for(int i=0;i<=n2;i++)
    {
        scanf("%c",s2+i);//input
        printf("%c",s2[i]);
    }
    int d=makeEqual(s1,n1,s2,n2);//function call
    printf("%d",d);//printing
    return 0;
}