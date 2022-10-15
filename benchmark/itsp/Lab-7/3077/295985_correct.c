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

int main() {
	char str[100];
	int i=0,n,j;
	scanf("%s",str);
    while(str[i]!='\0')      //checking last char
    {
        i++;        //string length
    }
    	scanf("%d",&n);     //taking input
	j=0;            //initialising
	n= n%26;
	while (j<i)
	{ 
	    if (str[j]<= 'z'-n)
	    {
	        str[j]= str[j]+n;
	        printf("%c",str[j]);
	        j++;
	    }
	    else if(str[j]>'z'-n)
	    {
	        str[j]= str[j]+(n-26);
	        printf("%c",str[j]);
	        j++;
	    }

	}
	
	
	return 0;
}