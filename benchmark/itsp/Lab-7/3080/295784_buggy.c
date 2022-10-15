/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"0"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"0"
*/
#include <stdio.h>

/*defining a function to find length of given string*/
int str_len(char a[100])
{
    int i=0;
    while(a[i]!='\0')
    {
        i++;
    }
    return i;
}
int main() {
	char str1[100],str2[100],ch;
	int n;
	/*storing the inputs given*/
	scanf("%s\n", str1);
	scanf("%c\n",&ch);
	scanf("%d\n",&n);
	scanf("%s\n", str2);
	int i,j,count=0;
	/*count will store the no. of 
	times ch comes in the given str1*/
	
	/*finding length of str1 and str2 */
	int length1=str_len(str1);
	int length2=str_len(str2);
	
	/*finding no of times ch appears in str1*/
	for(i=0;i<length1;i++)
	{
	    if(ch==str1[i])
	       count++;
	}
	
	/*checking whether str2 is a subsring of str1*/
	int res=0;
	for(i=0;i<length1;i++)
	{
	    if(str2[0]==str1[i])
	    {
	        for(j=0;j<length2;j++)
	           {
	               if(str2[j]!=str1[i+j])
	                break;
	           }
	       if(j==(length2)-1)
	         {res=1;break;}
	    }
	}
	printf("%d",res);
	
	
	
	return 0;
}