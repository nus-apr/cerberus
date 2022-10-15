/*numPass=8, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"NO"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int check_substr (char s1[], char s2[], int size1, int size2)
{                       //declaring fn to check substring
    int i=0, l, j=0;
    while (j<size1)
    {
        i=0;
        if (s2[i]==s1[j])
        {
            l=j;
            while (s2[i]!='\0')
            {
                if (s2[i]==s1[l])
                {
                    i=i+1;
                    l=l+1;
                }
                else
                    break;
                if (s2[i]=='\0')
                    return 1;
            }
        }
        else
            j=j+1;
    }
    return 0;
}
    
int c_less_n (char s1[], char ch, int size, int n)
{                       //declaring fn to check if c less than n
    int i;
    int count=0;
    for (i=0; s1[i]!='\0'; i++)
    { 
        if (s1[i] == ch)
        count = count + 1;
    }
    if (count < n)
        return 1;
    else
        return 0;
}

int main() 
    {
        char s1[100], s2[100], ch;  
        int n, i, j;    //declaring variables and arrays
        scanf ("%s ", s1);
        scanf ("%c", &ch);
        scanf ("%d", &n);
        scanf ("%s", s2);
                        //scanning input
        i = check_substr (s1, s2, 100, 100);
                        //checking if s2 substring of s1
        j = c_less_n (s1, ch, 100, n);
                        //checking if char c appears less than n times
        if ((i==1&&j==0)||(i==0&&j==1))
                        //satisfying exactly one condition
            printf ("YES");
        else            //printing output
            printf ("NO");

	// Fill this area with your code.
	    return 0;
    }