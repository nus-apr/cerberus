/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"eag"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"fagh"
Verdict:ACCEPTED, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"xcyz"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:ACCEPTED, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"labexma"
Verdict:ACCEPTED, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"apbqrst"
Verdict:ACCEPTED, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"prrsr"
Verdict:ACCEPTED, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"abdxcyz"
*/
#include <stdio.h>
#include <stdlib.h>

int check_lex(char* w, int n){
    int i, k=0;
    for(i=n-1; i>0; i--){
        if(*(w+i-1)<*(w+i)){
            k=i-1;
            break;
        }
    }
    return k;
}

void swap(char *w, int m, int n){
    char t;
    t=*(w+n);
    *(w+n)=*(w+m);
    *(w+m)=t;
}

void sort_lex(char* w, int x, int n){
    int i, j;
    for(i=n-1; i>x; i--){
        //j=x+1;
        for(j=x+1; j<i; j++){
             if(*(w+j)>*(w+j+1)){
                 swap(w,j,j+1);
             }
        }
    }
    
}

int main(){
    int n, i, k=1, x;
    char *w, var;
    scanf("%d\n", &n);
    w= (char*)calloc(n+1, sizeof(char));
    scanf("%s", w);
    for(i=0; i<(n-1); i++){
        if(*(w+i)<*(w+i+1)){
            k=0;
            break;
        }
    }
    
    if(k==1){
        printf("No Answer");
    }
    else{
        x=check_lex(w, n);
        var=(x+1);
        for(i= x+2; i<n; i++){
            if(*(w+i)>*(w+x) && *(w+i)<*(w+var)){
                var= i;
            }
        }
        swap(w,var, x);
        //printf("%s", w);
        /*t=*(var+w);
        *(var+w)=*(w+x);
        *(w+x)=t;*/
        sort_lex(w, x, n);
        printf("%s", w);
    }
    
    
    return 0;
}