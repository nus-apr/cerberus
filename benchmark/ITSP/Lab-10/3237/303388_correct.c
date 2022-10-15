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

int get_closest_word(char *, char **, int);

void add_swap(char **word1, char **word2){
    char *ptr;
    ptr=*word1;
    *word1=*word2;
    *word2=ptr;
}

int str_len(char str[]){
    int i;
    for(i=0;str[i]!='\0';i++);
    return i;
}

void get_dictionary(int N, char **dict){ //creates the dictionary
    int size,i;
    for(i=0;i<N;i++)
    {
        scanf("%d ",&size);
        dict[i]=(char *)malloc(sizeof(char)*(size+1));
        //each element of pointer array ponts to a string
        scanf("%s",dict[i]);
    }
}

void check_word(int N, char  **dict){ //checks input words
    int size,close;
    char *word;
    scanf("%d",&size);
    while(size!=-1) //leaves when input is -1
    {
        word=(char*)malloc(sizeof(char)*(size+1));
        //memory allocated for string
        scanf("%s",word);
        close=get_closest_word(word,dict,N);
        //gets index of string closest to word
        printf("%s\n",dict[close]);
        free(word);
        scanf("%d",&size);
    }
}

float get_closeless(char *word1, char *word2)
{
    int i,j,k,flag=0;
    float close=0;
    if(str_len(word1)==str_len(word2))
        close++; //+1 for equal length
    else
    {
        if(str_len(word2)<str_len(word1))
        {
            add_swap(&word1,&word2); //swap to make word1 smallest
            flag=1;
        }
        for(i=str_len(word1);i<str_len(word2);i++)
        {
           for(j=0;word1[j]!='\0';j++)
           {
               if(word2[i]==word1[j])
               {
                    close+=0.5;
            //+0.5 for character above length of smaller one string
                    break;
               }
           }
        }
    }
    for(i=0;word1[i]!='\0';i++)
    {
        if(word1[i]==word2[i])
            close+=2; //+2 for same letter
        else
        {
            for(j=0;word1[j]!='\0';j++)
            {
                if(word2[i]==word1[j])
                    break;
            }
            for(k=0;word2[k]!='\0';k++)
            {
                if(word1[i]==word2[k])
                    break;
            }
            if((word1[j]!='\0')&&(word2[k]!='\0'))
                close+=0.5; //+0.5
        }
    }
    if(flag==1)
    {
        add_swap(&word1,&word2); //swap again to regain initial address
    }
    return close;
}

int get_closest_word(char *word, char **dictionary, int N){
    float close,mclose;
    int i,index;
    mclose=get_closeless(word,dictionary[0]);
    index=0;
    for(i=1;i<N;i++)
    {
        close=get_closeless(word,dictionary[i]);
        //closeness calculated of word with each word in dictionary
        if(close>mclose)
        {
            mclose=close;
            index=i;
            //maximum closeness saved
        }
    }
    return index;
} 

int main(){
    char **dict;
    int N,i;
    scanf("%d\n",&N);
    dict=(char**)malloc(sizeof(char *)*N);
    get_dictionary(N,dict);//dictionary input taken
    check_word(N,dict);
    for(i=0;i<N;i++)
        free(dict[i]);
    free(dict);
    return 0;

}