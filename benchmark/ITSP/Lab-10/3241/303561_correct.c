/*numPass=5, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:ACCEPTED, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
#include <stdlib.h>
int gcd(int a,int b)
{
    if(a>b)
    return gcd(b,a);
    if(b%a==0)
    return a;
    return gcd(b%a,a);
}
int stringcmp(char*s1,char*s2,int a)
{
    int i;
  for(i=0;i<a;i++)
  {
      if(*(s1+i)!=*(s2+i))
      return 0;
  }
  return 1;
}
int check_fact(char*s1,int l,int a)
{
    int i;
    for(i=0;i<l;i=i+a)
    {
       if(stringcmp(s1,s1+i,a)!=1)
       return 0;
    }
    return 1;
}
int main()
{
    int l1,l2,i;
    scanf("%d",&l1);
    char*s1=(char*)malloc(l1*sizeof(char));
    scanf("%s",s1);
    scanf("%d",&l2);
    char*s2=(char*)malloc(l2*sizeof(char));
    scanf("%s",s2);
    int a=gcd(l1,l2);
    if(check_fact(s1,l1,a)&&check_fact(s2,l2,a))
    {
        for(i=0;i<a;i++)
        printf("%c",*(s1+i));
    }
	return 0 ; 
}