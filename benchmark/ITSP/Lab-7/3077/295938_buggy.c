/*numPass=6, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh""
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"zabc#"
Verdict:ACCEPTED, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghie"
Verdict:ACCEPTED, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"utz"
Verdict:ACCEPTED, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"a"
Verdict:ACCEPTED, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"zaza"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"thisproblemhasnoautomatedtestcases"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
*/
#include <stdio.h>
int read_s(char a[])     //to read the array
{   int i=0;
    int c=getchar();
   while(c!='\n'&&c!='\0')
   {  a[i]=c;
      c=getchar();
      i++;
   }
  return i;     //return length of array
}
int main() {
  int n,i;
  char arr[100];
 
  int l=read_s(arr);
  scanf("%d",&n);
 /* for(i=0;i<l;i++)    //print updated array
  {  putchar(arr[i]);
  }*/
  for(i=0;i<l;i++)    //updation
  { arr[i]=arr[i]+(n%26); 
    if(arr[i]>'z')
      arr[i]=arr[i]-26;
  }
  for(i=0;i<l;i++)    //print updated array
  {  putchar(arr[i]);
  }
	return 0;
}