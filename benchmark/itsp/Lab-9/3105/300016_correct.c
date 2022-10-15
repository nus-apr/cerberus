/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:"dlroW olleH"
Verdict:ACCEPTED, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:"Recursion Lab"
Verdict:ACCEPTED, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:"god yzal eht revo spmuj xof nworb kciuq ehT"
Verdict:ACCEPTED, Visibility:0, Input:"65
esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stI", ExpOutput:"Its vanished trees the trees that had made way for Gatsbys house

", Output:"Its vanished trees the trees that had made way for Gatsbys house"
*/
#include <stdio.h>
#include <string.h>
void revstr(char *c,int length)
{
    char temp;
    if(length==1||length==0)
    return;
    temp=c[0];
    c[0]=c[length-1];
    c[length-1]=temp;
    revstr(c+1,length-2);
}
int main()
{
    int n,i;
    scanf("%d\n",&n);
    char str[n];
    for(i=0;i<n;i++)
    {scanf("%c",&str[i]);}
    revstr(str,n-1);
    printf("%s",str);
    return (0);
}