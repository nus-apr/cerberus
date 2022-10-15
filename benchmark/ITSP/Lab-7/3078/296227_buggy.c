/*numPass=0, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"t", ExpOutput:"n", Output:""
Verdict:WRONG_ANSWER, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:""
Verdict:WRONG_ANSWER, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:""
*/
#include <stdio.h>
char transform(char a){
    if(a>='a'&&a<='m')
    return a+a-'a'+1;
    if(a>='n'&&a<='z')
    return a+a+1-'a'-26;
}
int length(char a[]){
    int i=0;
    while(a[i]!='\0'){
        i++;
    }
    return i;
}
void read_into_array(char a[]){
    int c=getchar();
    int i=0;
    while(c!='\n'){
        a[i]=c;
        c=getchar();
        i++;
    }
}

int main() {
	char a[100];
	read_into_array(a);
	int l=length(a);
	char c[100];
	for(int i=0;i<=l-1;i++){
	    c[i]=transform(a[i]);
	    printf("%c",c[i]);
	}
	return 0;
}