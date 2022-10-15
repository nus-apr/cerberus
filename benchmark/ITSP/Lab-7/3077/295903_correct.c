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
void modify_string(char str[100], int n)
{
    int i,k,m;
    for(i=0; str[i]!=0;++i)
    {
        if(str[i]+n<='z')
        {
            str[i]=str[i]+n;
        }
        else
        {
            k='z'-str[i];
            m=n-k-1;
            while(m>=26)
            {
                m=m-26;
            }
            str[i]='a'+m;
        }
    }
}
void print_string(char str[100])
{
    printf("%s",str);
}
int main() {
	// Fill this area with your code.
	char str[100];
	int n;
	scanf("%s",str);
	scanf("%d",&n);
	modify_string(str,n);
	print_string(str);
	return 0;
}