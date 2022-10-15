/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"zabc"
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
int read_s()     //to read the array
{   int i=0;
    int c=getchar();
   while(c!='\n'&&c!='\0')
   { 
      c=getchar();
      i++;
   }
  return i;     //return length of array
}
int main() {
  int n,i;
  char arr[100];
 
scanf("%s",arr);
  scanf("\n%d",&n);

  for(i=0;arr[i]!='\0';i++)    //updation
  { arr[i]=arr[i]+(n%26); 
    if(arr[i]>'z')
      arr[i]=arr[i]-26;
   
  }
  for(i=0;arr[i]!='\0';i++)    //print updated array
  {  putchar(arr[i]);
  }
	return 0;
}