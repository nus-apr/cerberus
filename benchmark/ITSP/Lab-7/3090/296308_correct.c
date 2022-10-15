/*numPass=9, numTotal=9
Verdict:ACCEPTED, Visibility:1, Input:"jhggd 
g 
sdfghjk", ExpOutput:"jhsdfghjkggd", Output:"jhsdfghjkggd"
Verdict:ACCEPTED, Visibility:1, Input:"abcde 
bc 
re", ExpOutput:"arebcde", Output:"arebcde"
Verdict:ACCEPTED, Visibility:1, Input:"jhukfi 
kf 
tred", ExpOutput:"jhutredkfi", Output:"jhutredkfi"
Verdict:ACCEPTED, Visibility:1, Input:"mississippi 
ss 
troll", ExpOutput:"mitrollssissippi", Output:"mitrollssissippi"
Verdict:ACCEPTED, Visibility:1, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
pre
com", ExpOutput:"Add-automated/compre-generated-test-cases-to-this-problem.", Output:"Add-automated/compre-generated-test-cases-to-this-problem."
Verdict:ACCEPTED, Visibility:0, Input:"mississippi 
pp 
troll", ExpOutput:"mississitrollppi", Output:"mississitrollppi"
Verdict:ACCEPTED, Visibility:0, Input:"underground
under
water", ExpOutput:"waterunderground", Output:"waterunderground"
Verdict:ACCEPTED, Visibility:0, Input:"imindian 
indian 
proud", ExpOutput:"improudindian", Output:"improudindian"
Verdict:ACCEPTED, Visibility:0, Input:"Add-automated/pre-generated-test-cases-to-this-problem.
/pre
-human", ExpOutput:"Add-automated-human/pre-generated-test-cases-to-this-problem.", Output:"Add-automated-human/pre-generated-test-cases-to-this-problem."
*/
#include <stdio.h>
int str_loc(char a[50], char b[50])
{
    int t = 0,m = 0,j = 0;
    while(b[j]!='\0')
    {
        j = 0;
        m = t;
        while(a[m] == b[j])
        {
            j++;
            m++;
        }
        t++;
    }
    return --t;
}
int main() {
	char str[50],s1[50],s2[50];
	scanf("%s",str);
	scanf("%s",s1);
	scanf("%s",s2);
	int n = str_loc(str,s1);
	char s3[50];
	int i = 0;
	for (; i < n; i++)
	{
	    s3[i] = str[i];
	}
	s3[i] = '\0';
	printf("%s%s",s3,s2);
	while(str[i]!='\0')
	{
	    printf("%c",str[i]);
	    i++;
	}
	return 0;
}