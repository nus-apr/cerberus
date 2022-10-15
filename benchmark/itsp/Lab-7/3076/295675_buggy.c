/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"abab", ExpOutput:"abab", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"a", ExpOutput:"a", Output:""
*/
#include <stdio.h>
 int len_ret(char character[])
 {
     int i=0;
     int c=0;
     while(character[i]=='\0'){
     c++;
     i++;
     }
     return c;
 }
int main() {
	char character[100];
	int s;
    scanf("%s",character);
    s=len_ret(character);
    
    if((s%2)==0)
    {
      for(int k=0;k<s/2;k++)
      {
          printf("%c",character[(s/2)+k]);
      }
      for(int j=0;j<s/2;j++)
      {
          printf("%c",character[j]);
      }
    }
    else if((s%2)!=0)
    {
        for(int m=0;m<(s-1)/2;m++)
        {
            printf("%c",character[((s+1)/2)+m]);
        }
        printf("%c",character[(s-1)/2]);
        for(int n=0;n<(s-1)/2;n++)
        {
            printf("%c",character[n]);
        }
    }
      return 0;
}