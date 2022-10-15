/*numPass=8, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcxy 
b 
hi", ExpOutput:"ahibcxy", Output:"ahibcxy"
Verdict:WRONG_ANSWER, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhsdfghjkgsdfghjkgd"
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
Verdict:ACCEPTED, Visibility:0, Input:"qwerty 
a 
zxcvb", ExpOutput:"qwerty", Output:"qwerty"
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
,
zxcvb", ExpOutput:"Thisproblemhasnoautomatedtestcases.", Output:"Thisproblemhasnoautomatedtestcases."
Verdict:ACCEPTED, Visibility:0, Input:"Thisproblemhasnoautomatedtestcases.
.
,,isn'tit?", ExpOutput:"Thisproblemhasnoautomatedtestcases,,isn'tit?.", Output:"Thisproblemhasnoautomatedtestcases,,isn'tit?."
*/
#include <stdio.h>

int main() {
	char A[50],B[50];
	char c;
	int i=0;
	scanf("%s\n%c\n%s",A,&c,B);
	while(A[i]!='\0'){
	    if(A[i]==c){
	        printf("%s",B);
	    }
	    printf("%c",A[i]);
	    i++;
	}
	return 0;
}