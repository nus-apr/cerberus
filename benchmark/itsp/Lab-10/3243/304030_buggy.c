/*numPass=2, numTotal=9
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
age", ExpOutput:"eag", Output:"age"
Verdict:ACCEPTED, Visibility:1, Input:"5
edcba", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
ahgf", ExpOutput:"fagh", Output:"ahgf"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
czyx", ExpOutput:"xcyz", Output:"czyx"
Verdict:ACCEPTED, Visibility:0, Input:"4
aaaa", ExpOutput:"No Answer", Output:"No Answer"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
labexam", ExpOutput:"labexma", Output:"labexam"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abtsrqp", ExpOutput:"apbqrst", Output:"abtsrqp"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
prrrs", ExpOutput:"prrsr", Output:"prrrs"
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
abdczyx", ExpOutput:"abdxcyz", Output:"abdczyx"
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

void swap(char m, char n){
    int t;
    t=n;
    n=m;
    m=t;
}

void sort_lex(char* w, int x, int n){
    int i, j;
    for(i=0; i<(n-x)*(n-x); n++){
        j=x+1;
        for(j=x+1; j<n-1; j++){
             if(*(w+j)>*(w+j+1)){
                 swap(*(w+j), *(w+j+1));
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
        swap(*(var+w), *(w+x));
        /*t=*(var+w);
        *(var+w)=*x;
        *x=t;*/
        sort_lex(w, x, n);
        printf("%s", w);
    }
    
    
    return 0;
}