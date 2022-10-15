/*numPass=7, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcxy 
b 
hi", ExpOutput:"ahibcxy", Output:"ahibcxy"
Verdict:ACCEPTED, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhsdfghjkggd"
Verdict:ACCEPTED, Visibility:1, Input:"dfghj 
j 
cvb", ExpOutput:"dfghcvbj", Output:"dfghcvbj"
Verdict:ACCEPTED, Visibility:1, Input:"d 
d 
asdfg", ExpOutput:"asdfgd", Output:"asdfgd"
Verdict:ACCEPTED, Visibility:1, Input:"Thisproblemhasnoautomatedtestcases.
.
----isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases----isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases----isn'tit?."
Verdict:ACCEPTED, Visibility:0, Input:"qwerty 
q 
zxcvb", ExpOutput:"zxcvbqwerty", Output:"zxcvbqwerty"
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty 
a 
zxcvb", ExpOutput:"qwerty", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
,
zxcvb", ExpOutput:"Thisproblemhasnoautomatedtestcases.", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
.
,,isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases,,isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases,,isn'tit?."
*/
#include <stdio.h>

int main() {
	// Fill this area with your code.
	char st[51];
	char sub[51];
	char c;
	scanf("%s",&st);
	scanf("%s",&c);
	scanf("%s",&sub);
	char ar[101];
	int a=0;
	//adding characters before c of st to array ar
	while(st[a]!=c)
	 {
	     if(st[a+1]=='\0') return 0;
	     ar[a]=st[a];
	     a++;
	 }
	 int b=0,d=a;
	 //adding chars of substring sub to array ar
	 while(sub[b]!='\0')
	 {
	     ar[a]=sub[b];
	     b++;a++;
	 }
	 //adding characters from char c of st to array ar
     while(st[d]!='\0')
     {
         ar[a]=st[d];
         a++;d++;
     }
     ar[a]='\0';
     printf("%s",ar);
	return 0;
}