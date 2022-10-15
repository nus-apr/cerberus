/*numPass=7, numTotal=7
Verdict:ACCEPTED, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"1 2 3 4 6 9 "
Verdict:ACCEPTED, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"-6 -4 -2 -1 1 2 3 4 5 6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"1 3 5 6 7 "
Verdict:ACCEPTED, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 2 9 "
Verdict:ACCEPTED, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"2 12 21 23 28 29 34 43 49 54 69 93 "
*/
#include <stdio.h>
#include <stdlib.h>

typedef struct set{
    
    int n;
    int *ar;
    
}set;

set *s3;

int assign(set *s1,set *s2){
    
    int i,j,a,k=0;
    
     for(i=0;i<s1->n;i++){
        
        (s3->ar)[k++]=(s1->ar)[i];
    
         }
    
    for(i=0;i<(s2->n);i++){
        
        a=0;
        
        for(j=0;j<(s1->n);j++){
            
            if((s2->ar)[i]==(s1->ar)[j]){
               
               a=1;
               break;    
            }     
          
            
        }
        
        if(a==0){
            
            (s3->ar)[k++]=(s2->ar)[i];
        } 
        
    }

    return k-1;

    
}

void sort(int n){
   
   int i,j,min,pos;    
       
       for(i=0;i<n;i++){
           
           min=(s3->ar)[i];   
           pos=i;    
            
            for(j=i+1;j<=n;j++){
               
               if((s3->ar)[j]<min){
                 
                 min=(s3->ar)[j];
                 pos=j;
              }
               
            }
             
             (s3->ar)[pos]=(s3->ar)[i];
             
             (s3->ar)[i]=min;
        
        } 

    
}

int main() {
   
   int i,j;
   
   set *s1,*s2;
    
    s1=(set*)malloc(sizeof(set));
    s2=(set*)malloc(sizeof(set));
    
      scanf("%d",&(s1->n));
    
        s1->ar=(int*)malloc((s1->n)*sizeof(int));
    
          for(i=0;i<(s1->n);i++){
             
             scanf("%d",(s1->ar)+i);
            }
    
    scanf("%d",&(s2->n));
    
    s2->ar=(int*)malloc((s2->n)*sizeof(int));
    
    for(i=0;i<(s2->n);i++){
        
        scanf("%d",(s2->ar)+i);
     }
    
    s3=(set*)malloc(sizeof(set));
    
    (s3->n)=(s1->n)+(s2->n);
    
     s3->ar=(int*)malloc((s3->n)*sizeof(int));
    
      j=assign(s1,s2);
    
       sort(j);
    
     for(i=0;i<=j;i++)
       
       printf("%d ",(s3->ar)[i]);
    
    return 0;

    
}