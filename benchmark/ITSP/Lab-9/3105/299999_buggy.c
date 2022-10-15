/*numPass=0, numTotal=4
Verdict:WRONG_ANSWER, Visibility:1, Input:"12
Hello World", ExpOutput:"dlroW olleH

", Output:"Hello WorlddlroW olleH"
Verdict:WRONG_ANSWER, Visibility:1, Input:"14
baL noisruceR", ExpOutput:"Recursion Lab

", Output:"baL noisruceRRecursion Lab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"44
The quick brown fox jumps over the lazy dog", ExpOutput:"god yzal eht revo spmuj xof nworb kciuq ehT

", Output:"The quick brown fox jumps over the lazy doggod yzal eht revo spmuj xof nworb kciuq ehT"
Verdict:WRONG_ANSWER, Visibility:0, Input:"65
esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stI", ExpOutput:"Its vanished trees the trees that had made way for Gatsbys house

", Output:"esuoh sybstaG rof yaw edam dah taht seert eht seert dehsinav stIIts vanished trees the trees that had made way for Gatsbys house"
*/
#include <stdio.h>
#include <string.h>
void str_rev(int n,char a[100])
{
    if(n==2) 
    printf("%c",a[0]);
    else 
    {
    printf("%c",a[n-2]);
     str_rev(n-1,a);
    }
}
int main()
{
    
  char str[100];
  int n,i;
  scanf("%d\n",&n);
  for(i=0;i<n-1;i++)
  {
      scanf("%c",&str[i]);
     printf("%c",str[i]);
  }
  str_rev(n,str);

     

    return 0;
}