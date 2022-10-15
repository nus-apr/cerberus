/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"4 hehe
6 hehehe", ExpOutput:"he", Output:"he"
Verdict:ACCEPTED, Visibility:1, Input:"4 abab
8 abababab", ExpOutput:"abab", Output:"abab"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 heeh
6 hehehe", ExpOutput:"", Output:"he"
Verdict:ACCEPTED, Visibility:0, Input:"5 hello
6 hihihi", ExpOutput:"", Output:""
Verdict:ACCEPTED, Visibility:0, Input:"1 a
5 aaaaa", ExpOutput:"a", Output:"a"
*/
#include <stdio.h>
#include <stdlib.h>

int _gcd(int a,int b)
{ return b?_gcd(b,a%b):a;
}

int main(){

    int n,m,p,i,j,k=0,gcd,q;
    scanf("%d ",&m);
    
    char *s1,*s2,*str,*str1,*str2,*sgcd;
    
    s1=(char*)malloc((m+1)*sizeof(char*));
     gets(s1);
    
    scanf("\n%d ",&n);
    s2=(char*)malloc((n+1)*sizeof(char*));
    str=(char*)malloc((n+1)*sizeof(char*));

    gets(s2);
    
    gcd=_gcd(m,n);
    
    if(n%m==0)
{      p=n/m;
    
    for(i=0;i<p;i++)
     for(j=0;j<m;j++)
     {str[k]=s1[j];
      k++;}
      
    str[k]='\0';
    
    j=0;
    
    for(i=0;i<n;i++)
      if(str[i]==s2[i])
      j++;
      
      if(j==n)
      printf("%s",s1);
}    

else
{
    p=m/gcd;
    q=n/gcd;
  sgcd=(char*)malloc((gcd+1)*sizeof(char*));
    
      str1=(char*)malloc((m+1)*sizeof(char*));
      
    for(i=0;i<gcd;i++)
      sgcd[i]=s1[i];
      sgcd[i]='\0';
      
      k=0;
    for(i=0;i<p;i++)
      for(j=0;j<gcd;j++)
      {str1[k]=sgcd[j];
      k++;}
      str1[k]='\0';
      
      str2=(char *)malloc((n+1)*sizeof(char*));
      k=0;
    for(i=0;i<q;i++)
      for(j=0;j<gcd;j++)
      {str2[k]=sgcd[j];
       k++;}
      str2[k]='\0';
      
      j=0;
       for(i=0;i<m;i++)
      if(str1[i]==s2[i])
      j++;
      
      k=0;
       for(i=0;i<n;i++)
      if(str2[i]==s2[i])
      k++;
      
      if(j==m && k==n)
          printf("%s",sgcd);
          
}          
	return 0 ; 
}