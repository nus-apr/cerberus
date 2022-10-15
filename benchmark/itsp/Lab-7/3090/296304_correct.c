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
int read_string(char s[])
{
    int ch,i=0;
    scanf("%s",s);//reads the string
    while(s[i++]!='\0');//finds size of string
    return i-1;//returns size
}

int check_substring(char str[],char s1[],int length,int length1)
//checks if s1 is substring of str
{
    int i,j,k;
    for(i=0;i<length;i++)
    {
        if(str[i]==s1[0])
        /*for substring first element of s1 should be in            str*/
        {
            for(j=0;j<length1;j++)
            {
                if(str[i+j]==s1[j])
                    k=1;
                else
                {
                    k=0;
                    break;
                }
            }
        if(k==1)//when entire s1 lies in str
        return i;//where substring lies in str            
        }
    }
    return 0;//in case s1 is not substring of str
}
int main()
{
    char str[50],s1[50],s2[50];
    int length,length1,length2,place,i,newlength;
	length=read_string(str);//gives size of str
	length1=read_string(s1);//gives size of s1
	length2=read_string(s2);//gives size of s2
	
	place=check_substring(str,s1,length,length1);
	//place from where elements of s1 are in str
	/*if(place==0)
	//if not a substring str printed as it is
	{
	    for(i=0;i<length;i++)
	    {
	        printf("%c",str[i]);
	    }
	}
	else*/
	//if s1 is substring then modifications done
	{
	    for(i=0;i<place;i++)
	    //prints str before place
	    {
	        printf("%c",str[i]);
	    }
	    for(i=0;i<length2;i++)
	    //prints elements of s2 now
	    {
	        printf("%c",s2[i]);
	    }
	    for(i=place;i<length;i++)
	    //prints remaining str
	    {
	        printf("%c",str[i]);
	    }
	}
	return 0;
}