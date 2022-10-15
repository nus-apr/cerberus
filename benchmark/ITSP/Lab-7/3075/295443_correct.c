/*numPass=9, numTotal=9
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
Verdict:ACCEPTED, Visibility:0, Input:"programming 
13", ExpOutput:"ngprogrammi", Output:"ngprogrammi"
Verdict:ACCEPTED, Visibility:0, Input:"abcde 
4", ExpOutput:"bcdea", Output:"bcdea"
Verdict:ACCEPTED, Visibility:0, Input:"abcdz 
5", ExpOutput:"abcdz", Output:"abcdz"
*/
#include <stdio.h>
int read(char a[]){
    int ch;
    int count=0;
    ch=a[count];
    while(ch!='\0'&&count<100){
        count=count+1;
        ch=a[count];
    }
    return count;
}
int main() {
	char a[100];
	int m,n;
	int i,j;
	scanf("%s",a);
	scanf("%d",&n);
		m=read(a);
n=n%m;
	for(i=m-n;i<m;i++){
	    printf("%c",a[i]);
	}
    for(j=0;j<m-n;j++){
        printf("%c",a[j]);
    }
	return 0;
}