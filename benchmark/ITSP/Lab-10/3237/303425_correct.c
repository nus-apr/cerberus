/*numPass=3, numTotal=3
Verdict:ACCEPTED, Visibility:1, Input:"3
2 hi
3 hey
4 yoyo
2 hi 
3 hiy 
4 yoy
1 h
-1
", ExpOutput:"hi
hey
yoyo
hi
", Output:"hi
hey
yoyo
hi
"
Verdict:ACCEPTED, Visibility:1, Input:"3 
8 Business
10 persuasion
11 intelligent
9 bussiness
8 business
10 persuation
10 inteligent
-1
", ExpOutput:"Business
Business
persuasion
intelligent
", Output:"Business
Business
persuasion
intelligent
"
Verdict:ACCEPTED, Visibility:0, Input:"3
5 hello
4 good
7 morning
4 helo
3 gud
6 mrnng
-1", ExpOutput:"hello
good
morning
", Output:"hello
good
morning
"
*/
#include <stdio.h>
#include <stdlib.h>

int min (int a , int b) {
    if (a>b){return b;}
    else{return a;}
}


float get_closeness(char *word1, char *word2) {
    int l1=0,l2=0;float score=0;
    while(*(word1+l1)!='\0') {l1++;}
    while(*(word2+l2)!='\0') {l2++;}
    if(l1==l2) {score++;}
    for (int i=0; i<min(l1,l2); i++) {
        if (*(word1+i)==*(word2+i)) {score=score+2;}
        else {
            for (int q=0; q<l2; q++) {
                if (*(word1+i)==*(word2+q)) {score=score+0.5;}
            }
        }
    }
    return score;
}

void get_closest_word(char *word, char **dictionary,int n) {
    int i,closest=0,maxscore=0,buffer;
    for (i=0; i<n; i++) {
        buffer=get_closeness(word,*(dictionary+i));
        if (buffer>maxscore) {maxscore=buffer;closest=i;}
    }
    printf("%s\n",*(dictionary+closest));
} 

int main(){
    int n,l,m=0;
    scanf("%d",&n);
    char *chkwrd;
    char **dictionary;
    char *word;
    dictionary = (char**)malloc(n*sizeof(char*));
    for(int k=0; k<n; k++) {
        scanf("%d",&l);
        word = (char*)malloc((l+1)*sizeof(char));
        scanf("%s",word);
        *(dictionary+k)=word;
        *(word+l)='\0';
    }
    //printf("%s",*(dictionary+2));
    //printf("%c",*(*(dictionary+2)+4));
    scanf("%d",&m);
      while(m!=(-1)) {
        chkwrd = (char*)malloc(m*sizeof(char));
        scanf("%s",chkwrd);
        get_closest_word(chkwrd,dictionary,n);
        free(chkwrd);
        scanf("%d",&m);
    } 
    
    return 0;
}