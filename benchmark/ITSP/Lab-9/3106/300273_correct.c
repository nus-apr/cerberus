/*numPass=4, numTotal=4
Verdict:ACCEPTED, Visibility:1, Input:"liril", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:1, Input:"oolaleloo", ExpOutput:"No
", Output:"No"
Verdict:ACCEPTED, Visibility:0, Input:"sorewaslerelsaweros", ExpOutput:"Yes
", Output:"Yes"
Verdict:ACCEPTED, Visibility:0, Input:"qwertyuiiuytrpwq", ExpOutput:"No
", Output:"No"
*/
#include <stdio.h>
#include <string.h>
 
int main()
{
    char word[20];
    scanf("%s",word);
    if(checkpal(word,0)==1)
    printf("Yes");
    else printf("No");
    return 0;
}
int checkpal(char word[],int position)
{
    int len;
    len=strlen(word)-(position+1);
    if (word[position]==word[len])
    {
        if((position+1)==len||(position==len))
        {
            return 1;
        }
        return checkpal(word,position+1);
    }
    else return 0;
}