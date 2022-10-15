/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"18 abcxyzdefxyzghixyz
3 xyz
2 uv", ExpOutput:"abcuvdefuvghiuv
", Output:"abcuvdefuvghiuv"
Verdict:ACCEPTED, Visibility:1, Input:"16 hello,howareyou?
3 are
4 were", ExpOutput:"hello,howwereyou?
", Output:"hello,howwereyou?"
Verdict:ACCEPTED, Visibility:1, Input:"20 abcdhefghighehiklmhe
2 he
4 hehe", ExpOutput:"abcdhehefghighehehiklmhehe
", Output:"abcdhehefghighehehiklmhehe"
Verdict:ACCEPTED, Visibility:1, Input:"18 hihellohihellohiih
2 hi 
5 hello", ExpOutput:"hellohellohellohellohelloih
", Output:"hellohellohellohellohelloih"
Verdict:ACCEPTED, Visibility:0, Input:"14 hihellohihello
3 hii
2 hi", ExpOutput:"hihellohihello
", Output:"hihellohihello"
*/
#include <stdio.h>
#include <stdlib.h>
int n,m,k;
char *scanstr(int p,char *s){
    s=(char *)malloc((p+1)*sizeof(char));
    s[p]='\0';
    scanf("%s\n",s);
    return s;
}

void replace_substring(char *s,char *t,char *w)
{
    int i,j,u,g,f=0;
    char *s4=(char *)malloc((n-m+k+5)*sizeof(char));
    for(g=0;g<n;g++){
        s4[g]=s[g];
    }
	for(i=0;i<n-m+1;i++){
	    for(j=0;j<m;j++){
	        if(s[i+j]==t[j]){
	            if(j==m-1){
	                for(u=i;u<i+k;u++){
	                    s4[u+(k-m)*f]=w[u-i];
	                }
	                for(u=i+k;u<n-m+k;u++){
	                    s4[u+(k-m)*f]=s[u-k+m];
	                }
	                f++;
	            }
	        }
	        else{
	            break;
	        }
	    }
	}
	s4[n+(k-m)*f]='\0';
	printf("%s",s4);
}

int main()
{
	scanf("%d ",&n);
	char *s1 = 0;
	s1=scanstr(n,s1);
    scanf("%d ",&m);
	char *s2 = 0;
	s2=scanstr(m,s2);
    scanf("%d ",&k);
	char *s3 = 0;
	s3=scanstr(k,s3);
	replace_substring(s1,s2,s3);

	return 0;

}