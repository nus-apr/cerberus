/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:"lroW olleH
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:"ecursion Lab
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:"od yzal eht revo spmuj xof nworb kciuq ehT
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"65
esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stI", ExpOutput:"Its vanished trees the trees that had made way for Gatsbys house

", Output:"ts vanished trees the trees that had made way for Gatsbys house
"
*/
#include <stdio.h>
#include <string.h>
void string_rev(char a[100],int m)
{if(m==2)
printf("%c",a[0]);
else 
   {printf("%c",a[m-2]);
    string_rev(a,m-1);
    }    
}
int main()
{char ch[100];int n;
scanf("%d",&n);
for(int i=0;i<=n;i++)
scanf("%c",&ch[i]);
string_rev(ch,n);    
return 0;
}