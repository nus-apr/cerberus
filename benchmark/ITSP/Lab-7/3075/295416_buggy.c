/*numPass=8, numTotal=9
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"programming"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>

int main() {
	// Fill this area with your code.
	char s[100];int i,l=0;
	scanf("%s",s);
	for(l=0;l<100;l++)
	    if(s[l]=='\0')
	        break;
	    else continue;     
	int n;
	scanf("%d",&n);
	for(i=l-n;i<l;i++)
	    printf("%c",s[i]);
	for(i=0;i<l-n;i++)
	    printf("%c",s[i]);

	return 0;
}