/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.
 - Use pointers only and when required allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks. All Strings are to be allocated dynamically 

You are given three strings s1, s2 and s2 as input. You need to replace all the occurrences of s2 in s1 by s3. Print the string s1 unchanged if s2 does not occur in s1.

For Example:
if the string s1 is "abcxyzdefxyzghixyz", 
s2 is "xyz",
s3 is "uv" then the output should be "abcuvdefuvghiuv"

INPUT FORMAT :
Three lines of input each of them are of the form "n s" where n is size of the input string s. 

For the above example :
INPUT:
18 abcxyzdefxyzghixyz
3 xyz
2 uv

OUTPUT:
abcuvdefuvghiuv

Note : You can assume that there would be no spaces in the input strings
*/
#include <stdio.h>
#include <stdlib.h>

int get_len(char s[])
{
	int i = 0 ; 
	while(s[i] != '\0')
		i++;

	return i ; 
}

int number_occourences(char *s, char *t){
	int s_len, t_len, i,j = 0; 

	int ncount, count = 0 ; 
	s_len = get_len(s);
	t_len = get_len(t);

	for(i = 0 ; i < s_len ; i++){
		ncount = 0 ; 
		for(j = 0 ; i + j < s_len  && j < t_len; j++)
			if(s[i+j] == t[j])
				ncount++;

		count =  count + ncount/t_len;
	} 

	return count;
}

int replace_substring(char *s,char *t,char *w)
{
	int j,i=0, k=0, index=-1,ncount=0;
	char *copy,*x,*y,*z;

	int s_len = get_len(s);
	int t_len = get_len(t);
	int w_len = get_len(w);

	int max_size_new = s_len + w_len*(number_occourences(s,t) + 1);
	copy = (char *)malloc(max_size_new * sizeof(char));

	for(i = 0 ; i < s_len ; i++){
		ncount = 0 ; 

		//checking if we have an occourence of a substring
		for(j = 0 ; i + j < s_len  && j < t_len; j++)
			if(s[i+j] == t[j])
				ncount++;

		// we have found an occourence
		if (ncount/t_len) {
			for(j = 0 ;j < w_len; j++)
				copy[k + j] = w[j];

			i = i + t_len - 1;
			k = k + w_len; 
		}
		else
		{
			copy[k] = s[i];
			k++ ;
		}
	} 

	printf("%s\n",copy);
}

int main()
{
	int n1, n2, n3;
	char *s, *t, *w;

	scanf("%d" , &n1);
	s = (char *)malloc((n1 + 1) * sizeof(char));
	scanf("%s",s);

	scanf("%d" , &n2);
	t = (char *)malloc((n2 + 1) * sizeof(char));
	scanf("%s",t);


	scanf("%d" , &n3);
	w = (char *)malloc((n3 + 1) * sizeof(char));
	scanf("%s",w);

	//printf("%d" , number_occourences(s,t));
	replace_substring(s,t,w);

	return 0;

}