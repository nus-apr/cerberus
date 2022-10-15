/*numPass=4, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"zbcd"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghif"
Verdict:ACCEPTED, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"utz"
Verdict:ACCEPTED, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"a"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"zbzb"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
*/
#include <stdio.h>

int main() {
	char str[101];
	int j,n,n1;
	scanf("%s",str);
	scanf("%d",&n);
	n1=n;
	if(n1>26)
	n1=n1%26;
	for(j=0;str[j]!='\0';j++)
	   {
	    str[j]=str[j]+n1;
	    if(str[j]>'z')
	    str[j]=str[j]+'a'-'z';
	   }
	printf("%s",str);
	return 0;
}