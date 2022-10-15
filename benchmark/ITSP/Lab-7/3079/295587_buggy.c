/*numPass=2, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcde 
bcd ", ExpOutput:"adcbe", Output:"abcde"
Verdict:ACCEPTED, Visibility:1, Input:"abcde 
acb ", ExpOutput:"abcde", Output:"abcde"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdebcd 
bcd ", ExpOutput:"adcbedcb", Output:"abcdebcd"
Verdict:ACCEPTED, Visibility:1, Input:"qwerty
t", ExpOutput:"qwerty", Output:"qwerty"
Verdict:WRONG_ANSWER, Visibility:0, Input:"manually
all", ExpOutput:"manullay", Output:"manually"
Verdict:WRONG_ANSWER, Visibility:0, Input:"iamesrever
esrever", ExpOutput:"iamreverse", Output:"iamesrever"
Verdict:WRONG_ANSWER, Visibility:0, Input:"youdogaredog
dog", ExpOutput:"yougodaregod", Output:"youdogaredog"
Verdict:WRONG_ANSWER, Visibility:0, Input:"ghhghghhghghhg
hhg", ExpOutput:"gghhhgghhhgghh", Output:"ghhghghhghghhg"
*/
#include <stdio.h>

int main() {
	char s1[100],s2[100];
	scanf("%s",s1);
	scanf("%s",s2);
	int i,j,k,count,m;
	for(count=0;count<100;count++)//length of string s2
	{
	    if(s2[count]=='\0')
	    {
	        break;
	    }
	}
	for(m=0;m<100;m++)
	{
	    if(s1[m]=='\0')//length of string s1
	    {
	        break;
	    }
	}
	int l;
	for(j=0;j<m;j++)
	{
	    for(k=0;k<count;k++)//to see if all elements of s2 are 
	    {                             //present in s1
	        l=0;
	        if(s2[k]==s1[j+k])
	        {
	            l++;
	        }
	    }
	    
	    if(l==count)
        {
            
	        for(i=0;i<count;i++)//reversing the elements
	        {
	            s1[j+count-1-i]=s2[i];
	        }
	        j=j+count;
	    }
	 }
	printf("%s",s1);
	return 0;
}