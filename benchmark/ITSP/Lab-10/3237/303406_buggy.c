/*numPass=2, numTotal=3
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
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 
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
intelligent
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

int N;

int strln(char arr[])
{
    int i=0;
    while(arr[i]!='\0')
    {
        i++;
    }
    return i;
}

int min(a,b)
{
    if (a>b) return b;
    else return a;
}



float get_closeless(char *word1, char *word2)
{
    int s1,s2,i;
    float k=0;
    s1=strln(word1);
    s2=strln(word2);
    if (s1==s2)
    {
        k++;//additional points for same length
    }
    for (i=0;i<(min(s1,s2));i++)
    {
        if (word1[i]==word2[i])
        {
            k=k+2;// if index by index matches 
        }
        if (word1[i]!=word2[i])
        {
            int j;
            if (s1>s2)
            {
                for (j=0;j<s1;j++)
                {
                    if (word2[i]==word1[j])// if there is char present
                    {
                        k=k+0.5;
                    }
                }
            }
            else
            {
                 for (j=0;j<s2;j++) // checking another way around.
                {
                    if (word2[i]==word1[j])
                    {
                        k=k+0.5;
                    }
                }
            }
        }
    }
    
    return k;
}

int get_closest_word(char *word, char **dictionary)
{
    float close,close2;
    int j,wordindex;
    close=get_closeless(word,dictionary[0]);//initializing the closeness
    wordindex=0;//initializing the index
   
    for (j=1;j<N;j++)
    {
        close2=get_closeless(word,dictionary[j]);
       
        if (close2>close)// if any other closer word is found 
        {
            wordindex=j;//word index get updated
        }
    }
    printf("%s\n",dictionary[wordindex]);
    return 0;
    
} 

int main()
{
    int b,i=0;
    char ** arr;
    char *arr2;
    scanf("%d",&N);
    arr = (char **)malloc(N * sizeof(char *));//allocating memory for dictionary 
    
    for(i = 0;i<N;i++)//runing loop for scaning the dictionary 
    {
        scanf("%d ",&b);
        arr[i] = (char *)malloc((b+1)*sizeof(char));
        scanf("%s \n",arr[i]);//storing dictionary
    }
    scanf("%d",&b);//initializing size of word
    while (b!=-1)//conditioning
    {
        
        arr2 = (char *)malloc((b+1)*sizeof(char));//allocating size
        scanf("%s \n",arr2);//scaning the word
        get_closest_word(arr2,arr);//geting closest word
        scanf("%d ",&b);//scaning next b;
        
    }
    
    
    return 0;
}