/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
#include <stdlib.h>
int gcd(int a,int b){
    if(a>b){
        if(b==0) return a;
        for(int i=0;(a!=0)&&(b!=0);i++){
            a=a%b;
            b=b%a;
        }
        return (b==0)?a:b;
    }
    if(a<b) return gcd(b,a);
}
void print_gcd(char s1[],char s2[],int n1,int n2){
    if(n1*n2==0){
        return;
    }
    if(n1==n2){
        int j;
        for(j=0;(s1[j]==s2[j])&&(j<n1);j++){
            ;
        }
        if(j==n1){
            printf("%s",s1);
        }
        else return;
    }
    if(n1<n2){
        if(n2%n1==0){
            int i,j;
            for(i=0;i<n1/n2;i++){
                for(j=0;(j<n1)&&(s1[j]==s2[n1*i+j]);j++){
                    ;
                }
                if(j!=n1) return;
            }
            printf("%s",s1);
        }
        if(n2%n1!=0){
            int i,j,k;
            for(i=1;i<n1/gcd(n2,n1);i++){
                for(j=0;(s1[j]==s1[gcd(n2,n1)*i+j])&&(j<gcd(n2,n1));j++){
                    ;
                }
                if(j!=gcd(n2,n1)) return;
            }
            for(i=1;i<n2/gcd(n2,n1);i++){
                for(j=0;(j<gcd(n2,n1))&&(s2[j]==s2[gcd(n2,n1)*i+j]);j++){
                    ;
                }
                if(j!=gcd(n2,n1)) return;
            }
            for(k=0;(k<gcd(n2,n1))&&(s1[k]==s2[k]);k++){
                ;
            }
            if(k!=gcd(n2,n1)) return;
            else{
                for(int i=0;i<gcd(n2,n1);i++){
                    printf("%c",s1[i]);
                }
            }
        }
    }
    if(n2<n1){
        return print_gcd(s2,s1,n2,n1);
    }
    
}

int main(){
    char *s1,*s2;
    int n1,n2;
    scanf("%d ",&n1);
    s1=(char *)malloc((n1+1)*sizeof(char));
    scanf("%s\n%d ",s1,&n2);
    s2=(char *)malloc((n2+1)*sizeof(char));
    scanf("%s",s2);
    print_gcd(s1,s2,n1,n2);
	return 0 ; 
}