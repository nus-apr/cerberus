/*numPass=2, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"codingisfun
i
2
true", ExpOutput:"NO
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:1, Input:"codingisfun
c
3
fun", ExpOutput:"NO
", Output:"YES"
Verdict:WRONG_ANSWER, Visibility:1, Input:"code
o
0
o ", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
0
o ", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"oo
o
2
o ", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
4
ll ", ExpOutput:"YES
", Output:"NO"
Verdict:WRONG_ANSWER, Visibility:0, Input:"atestcasemanually
a
5
ll ", ExpOutput:"NO
", Output:"YES"
Verdict:ACCEPTED, Visibility:0, Input:"atestcasemanually
a
4
atestcasemanually", ExpOutput:"YES
", Output:"YES"
*/
#include <stdio.h>

int count_char(char s[],char a){
    
    int count=0,i=0;
    while((s[i]!='\0')){
        
        if(s[i]==a){
            count++;
        }
       
        i++;
    }
    return count;
}

int check_substring(char s1[],char s2[]){
    int i,j=0,check;
    for(i=0;s1[i]!='\0';){
        if(s2[j]==s1[i]){
            check=1;
            ++i;
            ++j;
            continue;
        }
        else{
            check=0;
            break;
        }
    }
    return check;
}

int main() {
    int n,count,check=0;
    char c,s1[100],s2[100];
	scanf("%s\n",s1);
	scanf("%c %d\n",&c,&n);
	scanf("%s",s2);

	count=count_char(s1,c);
	if(count<n){
	    check++;
	}
	check=check+check_substring(s1,s2);
	if(check==1){
	    printf("YES");
	}
	else{
	    printf("NO");
	}
	return 0;
}