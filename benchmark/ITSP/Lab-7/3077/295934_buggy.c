/*numPass=2, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"z{|}"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"jklm"
Verdict:WRONG_ANSWER, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"a"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"z{z{"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"|{{{~}{"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"}|||~|"
*/
#include <stdio.h>

int main() {
char str[100];
int n,i=0;
scanf("%s\n%d",&str,&n);
for(;str[i]!=0;i++);

for(int k=0;k<i;k++)  {
    str[k]+=n;    
}

printf("%s",str);
	return 0;
}