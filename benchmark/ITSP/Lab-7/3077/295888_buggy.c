/*numPass=6, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"zabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"jklmi"
Verdict:WRONG_ANSWER, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:""
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

int main() {
	char str[100];
	int n,i=0;
	scanf("%s\n%d",str,&n);
	while(str[i]!='\0'){
	    str[i]=str[i]+n;
	    if(str[i]>'z'){
	        str[i]=str[i]-26;
	    }
	    i++;
	}
	printf("%s",str);
	return 0;
}