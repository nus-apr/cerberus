/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"bdfhjl", Output:"bdfhjl"
Verdict:ACCEPTED, Visibility:1, Input:"wxyz", ExpOutput:"tvxz", Output:"tvxz"
Verdict:ACCEPTED, Visibility:1, Input:"zyxw", ExpOutput:"zxvt", Output:"zxvt"
Verdict:ACCEPTED, Visibility:1, Input:"t", ExpOutput:"n", Output:"n"
Verdict:ACCEPTED, Visibility:1, Input:"lly", ExpOutput:"xxx", Output:"xxx"
Verdict:ACCEPTED, Visibility:0, Input:"qwerty", ExpOutput:"htjjnx", Output:"htjjnx"
Verdict:ACCEPTED, Visibility:0, Input:"manuallyaddedtestcases", ExpOutput:"zbbpbxxxbhhjhnjlnfbljl", Output:"zbbpbxxxbhhjhnjlnfbljl"
Verdict:ACCEPTED, Visibility:0, Input:"yllyl", ExpOutput:"xxxxx", Output:"xxxxx"
Verdict:ACCEPTED, Visibility:0, Input:"visibility", ExpOutput:"rrlrdrxrnx", Output:"rrlrdrxrnx"
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
    while(c!=EOF){
        a[i]=c;
        c=getchar();
        i++;
    }
    a[i]='\0';
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