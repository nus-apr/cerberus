/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"1 4 5", ExpOutput:"1111
1  1
1  1
1  1
1111
", Output:"1111
1  1
1  1
1  1
1111"
Verdict:ACCEPTED, Visibility:1, Input:"2 5 6", ExpOutput:"22222
2   2
2   2
2   2
2   2
22222
", Output:"22222
2   2
2   2
2   2
2   2
22222"
Verdict:ACCEPTED, Visibility:1, Input:"9 6 7", ExpOutput:"999999
9    9
9    9
9    9
9    9
9    9
999999
", Output:"999999
9    9
9    9
9    9
9    9
9    9
999999"
Verdict:ACCEPTED, Visibility:1, Input:"3 4 5", ExpOutput:"3333
3  3
3  3
3  3
3333
", Output:"3333
3  3
3  3
3  3
3333"
Verdict:ACCEPTED, Visibility:1, Input:"2 2 2", ExpOutput:"22
22
", Output:"22
22"
Verdict:ACCEPTED, Visibility:0, Input:"3 3 3", ExpOutput:"333
3 3
333
", Output:"333
3 3
333"
Verdict:ACCEPTED, Visibility:0, Input:"1 1 1", ExpOutput:"1
", Output:"1"
*/
#include<stdio.h>

int main() {
	int N,w,h,i,j,k,l,m,n;
	scanf("%d",&N);
	scanf("%d",&w);
	scanf("%d",&h);
	if(w==1){
	    if(h==1){
	    printf("%d",N);
	    }
	    else{
	    for(m=0;m<h;m++)
	    {
	     printf("%d\n",N);
	    }
	}
	}
	else{
	    if(h==1){
	        printf("%d",N);
	        for(n=0;n<w-2;n++)
	        {
	            printf(" ");
	        }
	        printf("%d",N);
	    }
	    else{
	
	        {
	         for(i=0;i<w;i++)
             {
              printf("%d",N);
             }
              printf("\n");
	        }
	
	
	        {
	         for(j=0;j<(h-2);j++)
	         {
	          printf("%d",N);
	         {	   
	          for(k=0;k<(w-2);k++)
	          {
	           printf(" ");
	           }   
	          }
	           printf("%d\n",N);
	          }
	          }
	
	
	          {   
	            for(l=0;l<w;l++)
	            {
	             printf("%d",N);
	             }
               }
     
	    }
	 }
	return 0;
}