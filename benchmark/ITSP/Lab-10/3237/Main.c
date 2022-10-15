/*
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template.
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you will get 0 marks. All Strings and Dictionaries, etc should be dynamically allocated. 

One of our tutors, named A,  is very bad in typing. He tried to type without looking at the keyboard and ends up making a lot of mistakes. For example, he sometimes ends up with "helli" instead of "hello", "chariman" for "chairman", etc.  A is very sad as he can not compose mails, write question papers, etc quickly.  Please help A by writing a program which tells him the closest word in the dictionary for input words. 

Closeness of two word strings s1 and s2 is computed as follows:
1. If length(s1) = length(s2) then you get 1 additional points of closeness. 
2. For each j such that s1[j] = s2[j], you get 2 additional points.
3. For each j such that s1[j] != s2[j], you get 0.5 addition points if s1[j] exists in s2 and s2[j] exists in s1. In the situations where j >= length(s1) but j < length(s2), you only need to check if s2[j] exists in s1 and similarly if j < length(s1) and j >= length(s2). 

For Example, Closeness between "hello" and "helobo" is 7.0. Closeness between "persuasion" and  "perturbation" is 10.5. (The smaller the closeness parameter, the closer the strings are!)

INPUT : 
You would be given the size N of the dictionary. This would be followed by N lines each of which has a number followed by a string. The number denotes the length of this string. These N lines constitute the contents of the dictionary. 
This is followed by string-length and string pairs which are the words to be corrected based on their closeness in the dictionary. Input pairs should be processed till you see a -1. 
 
OUTPUT :
Print the closest string in the dictionary corresponding to each length, string pair. If there exists multiple words in the dictionary which are equally close to the input word then output the one which was added earlier to the dictionary. 

EXAMPLE:
Input : 
3
2 hi
3 hey
4 yoyo
2 hi 
3 hiy 
4 yoy
1 h
-1

Output :
hi 
hey 
yoyo 
hi

NOTE : 
Words like "hi" and "Hi" should be treated as different words in the dictionary. You can make your program case insensitive as a practice problems. There are many heuristics which are used to correct a mistyped word based on a dictionary. The closeness measure defined for this problem is one of them. There may exists better heuristics.
*/
#include <stdio.h>
#include <stdlib.h>

int get_len(char s[])
{
	int i = 0 ; 
	while(*(s + i) != '\0')
		i++;

	return i ; 
}

int exists(char *a , char ch){
	int i = 0 ; 
	while(a[i] != '\0')
	{
		if(a[i] == ch)
			return 1; 
		i++; 
	}

	return 0;
}

float get_closeless(char *a, char *b)
{
	float closeness = 0 ;
	int i , j;

	int a_len = get_len(a) , b_len = get_len(b); 

	if(a_len == b_len)
		closeness += 1; 

	for(i = 0 ; i < a_len || i < b_len ; i++)
		if(i < a_len && i < b_len)
		{	if(a[i] == b[i])
				closeness += 2;
			else {if (exists(b , a[i]) && exists(a , b[i]))
				closeness += 0.5;}	
		}
		else{
			if(i < a_len){
				if(exists(b, a[i]))
				{ 
					closeness += 0.5; 
				}
			}
			else if(exists(a, b[i])){
				closeness += 0.5;
			}

		}

	return closeness ; 
}

int get_closest_word(char *s, char **dict){
	int i = 0 ; 
	int max_closeness = - 1; 
	int max_closeness_index = -1;
	while(dict[i] != NULL ){
		if(get_closeless(s , dict[i]) > max_closeness){
			max_closeness = get_closeless(s, dict[i]) ; 
			max_closeness_index = i ; 
		}
		i++;
	} 
	return max_closeness_index ;
} 

int main(){
	int n, n_temp , e_len, i, j;
	char *error_word = NULL ;

	scanf("%d" , &n);

	char **dict = malloc((n + 1)*sizeof(int *));
	for (i=0 ; i<n ; i++){
			scanf("%d" , &n_temp);
            dict[i] = malloc((n_temp + 1)*sizeof(int));
            scanf("%s" , dict[i]);
        }
    dict[n] = NULL ;

    while(1){
    	scanf("%d" , &n_temp);
    	if(n_temp == - 1)
    		break;

    	free(error_word);
    	error_word = malloc((n_temp + 1)*sizeof(char));
    	scanf("%s", error_word);
    	printf("%s\n",dict[get_closest_word(error_word , dict)]);
    	
    }
    return 0;

}