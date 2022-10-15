/*numPass=5, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"z{|}"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghi"
Verdict:ACCEPTED, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"utz"
Verdict:ACCEPTED, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"a"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"z{z{"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"thisproblemhasnoautomatedtestcases"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
*/
#include <stdio.h>
/*char alpha(char a)
{
    if(a>'z')
    return alpha(a-26);
    return a;
}*/
int main() {
    char arr[100];
	int n,j,i=0;
	arr[0]=getchar();
	while(arr[i]!='\n'&&arr[i]!='\0'&&arr[i]!=' ')
	{
	    i++;
	    arr[i]=getchar();
	}
	scanf("%d",&n);
	n=n%26;
	for(j=0;j<i;j++)
	{
	    arr[j]=arr[j]+n;
	    printf("%c",arr[j]);
	}
	
	return 0;
}