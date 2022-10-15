/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef
2", ExpOutput:"efabcd", Output:"efabcd"
Verdict:ACCEPTED, Visibility:1, Input:"programming 
11", ExpOutput:"programming", Output:"programming"
Verdict:ACCEPTED, Visibility:1, Input:"hello-@programmer 
5", ExpOutput:"ammerhello-@progr", Output:"ammerhello-@progr"
Verdict:ACCEPTED, Visibility:0, Input:"hellodear 
3", ExpOutput:"earhellod", Output:"earhellod"
Verdict:ACCEPTED, Visibility:0, Input:"progamming 
0", ExpOutput:"progamming", Output:"progamming"
Verdict:ACCEPTED, Visibility:0, Input:"programming
10", ExpOutput:"rogrammingp", Output:"rogrammingp"
Verdict:ACCEPTED, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"ngprogrammi"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>
void right_rotate(char s[],int);

int main() {
    char str[101];
    int n;
    scanf("%s%d",str,&n);
    right_rotate(str,n);
    printf("%s",str);

	return 0;
}

void right_rotate(char str[],int n)
{
    char str1[101];
    int len=0;
    while(str[len]!='\0')
     {
         len++;
     }
    int i,j;
    for(i=0;i<len;++i)
     {
         if(i+n>=len)
          j=(i+n)%len;
         else
          j=i+n;
         str1[j]=str[i]; 
     }
    for(i=0;i<len;i++)
      str[i]=str1[i];
}
