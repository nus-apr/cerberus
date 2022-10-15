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

int slen(char* s){
    int i=0;
    while(s[i]){
        i++;
    }
    return i;
}
void replace_substring(char* t,char*s,char*w){
    int l1=slen(t);
    int l2=slen(s);
    int* a;
    a=(int *)malloc((l1+1)*sizeof(int));
    for(int i=0;i<l1+1;i++){
        a[i]=-1;
    }
    for(int i=0;i<l1-l2+1;i++){
        int k=0;
        for(int j=0;j<l2;j++){
            if(t[i+j]==s[j]){k+=1;}
        }if(k==l2){a[i]=i;}
    }
    for(int i=0;i<l1;i++){
        if(a[i]==i){
            printf("%s",w);
            i=i+l2-1;
        }else{
            putchar(t[i]);
        }
    }
    free(a);
    return;
}

int main()
{int n;
char* s1; 
scanf("%d",&n);
s1=(char*)malloc((n+1)*sizeof(char));
    
    scanf("%s",s1);
  

int m;
char* s2; 
scanf("%d",&m);
s2=(char*)malloc((m+1)*sizeof(char));

    scanf("%s",s2);
    

int k;
char* s3; 
scanf("%d",&k);
s3=(char*)malloc((k+1)*sizeof(char));

    scanf("%s",s3);
    replace_substring(s1,s2,s3);

free(s3);
free(s2);
free(s1);
	return 0;

}