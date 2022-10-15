/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"5
1 -2 3 -5 5", ExpOutput:"3
", Output:"3"
Verdict:ACCEPTED, Visibility:1, Input:"9
1 2 -9 3 21 5 41 6 70", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:1, Input:"5
-1 2 5 -7 9", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:1, Input:"9
21 23 1 34 123 324 12 213 3423", ExpOutput:"6
", Output:"6"
Verdict:ACCEPTED, Visibility:0, Input:"6
99 -12 14 56 987 34", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"5
-1 45 98 -2 103", ExpOutput:"4
", Output:"4"
Verdict:ACCEPTED, Visibility:0, Input:"3
1 -2 46", ExpOutput:"2
", Output:"2"
*/
#include <stdio.h>
int Length(int s[],int i){
    int seq[20],t,j,k,b,m,c;
    int count=0;
    
    for(j=0;j<i;j++){
        count=0;
        
        for(b=j+1;b<i&&b>j;b++){
            
            c=0;
            for(m=1;m<b-j+1;m++){
                if (s[b]>s[b-m]) c=c+1;
            }
            
            if(s[j]<s[b]&&c == b-j) count = count +1;
            else continue;
                
        }
        
        seq[j]=count+1;
        
    }
    
    int a; int num = 0;
    for(t=0;t<i;t++){
        num=0;
        for(k=0;k<i;k++){
            if(seq[t]>=seq[k]) num = num+1;
        }
        if (num==i) a = seq[t];
            
             
    }
    return a;
}

int max(int a,int b){
    if(a>=b) return a;
    else return b;
}

int main() {
	int N,i;
	scanf("%d",&N);
	int A[N];
	for(i=0;i<N;i++){           
	    scanf("%d",&A[i]);
	}
    
    printf("%d",Length(A,N));
    
    
    
	return 0;
}