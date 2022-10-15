/*numPass=3, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefgh"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"`abc	"
Verdict:ACCEPTED, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghie"
Verdict:WRONG_ANSWER, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"ut`"
Verdict:WRONG_ANSWER, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"G"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"`a`a"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"thisproblemhGsnoGutomGtedtestcGses"
Verdict:ACCEPTED, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtft"
*/
#include <stdio.h>

int read(char a[]){
    int i,count=0;
    char c;
    c=getchar();
    for(i=0;c!='\n';i++){
        a[i]=c;
        count=count+1;
        c=getchar();
    }
    
    a[count]='\0';
    return count;
}

void shift(char a[],int n,int count){
    int i,l,p;
    char c;
    l=n%26;
    for(i=0;i<count;i++){
        c=a[i]+l;
        if((c<='a')||(c>='z')){
            p=a[i]+l-'z';
            c='a'+p-1;
        }
        printf("%c",c);
    }
    
    
}

int main() {
	char a[100];
	int n,b;
	b = read(a);
	scanf("\n%d",&n);
	shift(a,n,b);
	
	return 0;
}