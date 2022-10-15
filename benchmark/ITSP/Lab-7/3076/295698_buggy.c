/*numPass=4, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"abcdef", ExpOutput:"defabc", Output:"defabc"
Verdict:WRONG_ANSWER, Visibility:1, Input:"programming", ExpOutput:"mmingaprogr", Output:"mmingamming"
Verdict:WRONG_ANSWER, Visibility:1, Input:"hello-@programmer", ExpOutput:"ogrammerrhello-@p", Output:"ogrammerrogrammer"
Verdict:ACCEPTED, Visibility:1, Input:"abab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:0, Input:"hellodear", ExpOutput:"dearohell", Output:"dearodear"
Verdict:ACCEPTED, Visibility:0, Input:"progamming", ExpOutput:"mmingproga", Output:"mmingproga"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abcdz", ExpOutput:"dzcab", Output:"dzcdz"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abc", ExpOutput:"cba", Output:"cbc"
Verdict:ACCEPTED, Visibility:0, Input:"a", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
int str_len (char str[], int size)
    {
        int i=0;
        while (str[i]!='\0')
            i++;
        return i;
    }

int main()
    {
        char ar[100];
        int len, i, tmp;
        scanf ("%s", ar);
        len = str_len (ar, 100);
        for (i=0; i<len/2; i++)
            {
                if (len%2 == 0)
                    {
                        tmp = ar[i];
                        ar[i] = ar[len/2 + i];
                        ar[len/2 + i] = tmp;
                    }
                else
                    {
                        tmp = ar[i];
                        ar [i] = ar[len/2 + 1 + i];
                        ar[len/2 + 1 + i] = ar[i];
                    }
            }
        printf ("%s", ar);
	// Fill this area with your code.
	return 0;
    }