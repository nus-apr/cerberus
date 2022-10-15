/*numPass=7, numTotal=8
Verdict:ACCEPTED, Visibility:1, Input:"3 4
0 1 1 0
1 0 0 1
1 0 2 3", ExpOutput:"2 1 3
", Output:"2 1 3"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
1 0 0 0 0
0 1 0 0 0
0 0 1 0 0
0 0 0 1 0
0 0 0 0 1", ExpOutput:"5 1 1
", Output:"5 1 1"
Verdict:ACCEPTED, Visibility:1, Input:"2 2
0 2
3 4", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"1 1
0", ExpOutput:"0 -1 -1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:1, Input:"5 5
3 2 3 4 5
1 2 3 4 5
6 7 8 9 10
11 23 5 5 5
-1 2 3 4 5", ExpOutput:"1 2 1
", Output:"1 2 1"
Verdict:ACCEPTED, Visibility:0, Input:"5 2
1 0
0 1
0 0
1 0
0 1", ExpOutput:"2 1 1
", Output:"2 1 1"
Verdict:WRONG_ANSWER, Visibility:0, Input:"1 1
1", ExpOutput:"1 1 1
", Output:"0 -1 -1"
Verdict:ACCEPTED, Visibility:0, Input:"10 10
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
-1 -1 -1 -1 -1 -1 -1 -1 -1 -1
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
1 0 0 0 0 0 0 0 0 0
0 1 0 0 0 0 0 0 0 0
0 0 1 0 0 0 0 0 0 0", ExpOutput:"3 8 1
", Output:"3 8 1"
*/
#include <stdio.h>

int good(int a[20][20],int i,int j,int m,int n,int d);//This is the prototype for good() which will check whether the square matrix of dimension d*d with a[i][j] as the top left element is an identity matrix,if yes,then it will return d else 0

int good(int a[20][20],int i,int j,int m,int n,int d){
  
  int p,q,check=-1;
   
   
     for(p=0;p<=d;p++)
      
      for(q=0;q<=d;q++)
        
        if(!(((p==q)&&(a[i+p][j+q]==1))||((p!=q)&&(a[i+p][j+q]==0)))){
            
            check=0;
            return 0;
            break;
        }
        
       
     
     if(check==-1)
      
      return d+1; 
     
        
  }

int main(){

int a[20][20],m,n,i,j,d,g=0,l,i1,j1;
  
  scanf("%d %d",&m,&n);
   
   for(i=0;i<m;i++)
    
    for(j=0;j<n;j++)
      
      scanf("%d ",&a[i][j]);
  
   for(i=0;i<m-1;i++)
   
    for(j=0;j<n-1;j++){
      
       if(a[i][j]==1){//good will be called only when a[i][j]=1
       
        for(l=0;(i+l)<m&&(j+l)<n;l++){
           
           d=good(a,i,j,m,n,l); 
         
            if(d!=0){
         
               if(d>g){
         
                  g=d;
                  i1=i;
                  j1=j;  
         
               }
         
            else if(g==d){
            
               if((i<i1)||((i==i1)&&(j<j1)))
                 i1=i;j1=j;    
    
              }
           
          }   
      
        }    
     
           
     }
       
   }
    
    if(g==0){
        
        printf("%d %d %d",g,-1,-1);
    
        }
    
    else{
        
        printf("%d %d %d",g,i1+1,j1+1);    
        
      }
    
    return 0;

 }