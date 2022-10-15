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
void print_rev(char s[],int slength,int i)
{   if(i>(slength-2))
    return;
    if(i==(slength-2))
    {
    printf("%c",s[i]);
    return;
    }
    else
    {
        print_rev(s,slength,i+1);
        printf("%c",s[i]);
    }
}
int main()
{
    char s[100];
    int  slength,i=0;
    scanf("%d\n",&slength);
    while(i!=slength-1)
    {
        scanf("%c",&s[i]);
        i++;
    }
    s[i]='\0';
    i=0;
   print_rev(s,slength,i); 
    return 0;
}