/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"liril", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"oolaleloo", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"sorewaslerelsaweros", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"qwertyuiiuytrpwq", ExpOutput:"No
", Output:"No"
*/
#include <stdio.h>
#include <string.h>
 
int pali(char str[100],int end,int start)
{
    if(start>=end)
    return 1;
    if(str[end]!=str[start])
    return 0;
   return pali(str,--end,++start);
    return 1;
  /* 
  //  static int i=0;
    printf("%d\n",i);
    if(i>n/2)
    {
        return 0;
    }
    if(str[l-1]!=str[i])
    {
        return 0;
    }
    
    pali(str,n,l-1,++i);
    return 1;*/
}

int main()
{
    char str[100];
    scanf("%s",str);
    int l=strlen(str);
 
    int res=pali(str,l-1,0);
   // printf("%d %d",l,res);
   if(res==1)
   printf("Yes");
   else printf("No");
    return 0;
}