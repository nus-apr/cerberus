/*numPass=0, numTotal=8
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdef 
2 ", ExpOutput:"cdefgh", Output:"cdefghP"
Verdict:WRONG_ANSWER, Visibility:1, Input:"wxyz 
3", ExpOutput:"zabc", Output:"zabcQ"
Verdict:WRONG_ANSWER, Visibility:1, Input:"abcdz
265", ExpOutput:"fghie", Output:"fghiem"
Verdict:WRONG_ANSWER, Visibility:1, Input:"pou
2605", ExpOutput:"utz", Output:"utzm"
Verdict:WRONG_ANSWER, Visibility:0, Input:"a
0", ExpOutput:"a", Output:"aN"
Verdict:WRONG_ANSWER, Visibility:0, Input:"abab
25", ExpOutput:"zaza", Output:"zazaM"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
26", ExpOutput:"thisproblemhasnoautomatedtestcases", Output:"thisproblemhasnoautomatedtestcasesN"
Verdict:WRONG_ANSWER, Visibility:0, Input:"thisproblemhasnoautomatedtestcases
27", ExpOutput:"uijtqspcmfnibtopbvupnbufeuftudbtft", Output:"uijtqspcmfnibtopbvupnbufeuftudbtftO	"
*/
#include <stdio.h>

int main() {
	
	char arr1[100], arr2[100];
	int i,n,j,k=0,l;
	
	scanf("%s",arr1);//scan the string to be operated...
	
	for(i=0;arr1[i]!='\0';i++){
	    continue;//count the number of terms in the string...
	}

	scanf("%d",&n);//No. of shifting to be done...
	
/*	for(j=0;j<=i;j++){//operation on array...
	    if( (arr1[k]+n<='z') && arr1[k]+n>='a'){
	        arr2[j]=arr1[k]+n;
	    }
	    else{
	         p=arr1[k]+(n%26);
	        
	        if((arr1[k]+(n%26)<='z') && (arr1[k]+(n%26)>='a')){
	         p=arr2[j] ;  
	        }
	    }
	    
	    k++;
	}
	*/
	
	for(j=0; j <=i; j++){
	    arr2[j] = 'a' + (arr1[k]-'a'+n)%26;
	    k++;
	}
	
	    
	for(l=0;l<=j;l++){//printing the resultant array...
	    printf("%c",arr2[l]);
	}
	
	
	
	
	 
	return 0;
}