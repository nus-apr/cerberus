/*numPass=0, numTotal=6
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12", ExpOutput:"1
2
4
3
", Output:"3421"
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
13745 30 59 50
12845 31 23 50
12424 31 23 40
", ExpOutput:"12845
13745
12424
", Output:"124241374512845"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 50 20 30
4 30 40 10
2 40 40 10
3 35 29 40", ExpOutput:"3
1
2
4
", Output:"4213"
Verdict:WRONG_ANSWER, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"21"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"2143"
Verdict:WRONG_ANSWER, Visibility:0, Input:"5
1 50 50 30
2 20 30 50
3 80 50 66 
4 10 29 10
5 10 10 10", ExpOutput:"3
2
1
4
5
", Output:"54123"
*/
#include <stdio.h>
#include <stdlib.h>
 typedef struct marks{
      int no;
      int phy;
      int chm;
      int mth;
  } m;
  /*typedef struct ni{
    
  }
  int find_max(m* a,int i,int j){
      int k=(*a).mth;
      int o
      for(int z=0;z<(i-j);z++){
          if((*(a+z)>k){
              o=k;
          }
      }
      return o;
  }*/
  void swap(m *a,int i,int j){
      m t=a[i];
      a[i]=a[j];
      a[j]=t;
  }
 /* void sort(m *a,int start,int end){
      
      if(start==end){
          return;
      }
      ind_max= find_max(a,start,end);
      swap(a,ind_max,start);
      sort(a,start+1,end);
  }*/
  void rank(m *a,int n){
      int i,j;
//int *d;
      for( i=0;i<n;i++){
          for( j=0;j<n-i-1;j++){
              if((*(a+j)).mth>(*(a+j+1)).mth){
                  swap(a,j,j+1);
              }
              if((*(a+j)).mth==(*(a+j+1)).mth){
                  if((*(a+j)).phy>(*(a+j+1)).phy){
                      swap(a,j,j+1);
                  }
                  if((*(a+j)).phy==(*(a+j+1)).phy){
                      if((*(a+j)).chm>(*(a+j+1)).chm){
                          swap(a,j,j+1);
                      }
                  }
              }
          }
      }
      for(int i=0;i<n;i++){
          printf("%d",a[i].no);
      }
  }
  
int main() {
  m *a;
  int n;
  scanf("%d\n",&n);
  
  a=(m*)malloc(n*sizeof(m));
  for(int i=0;i<n;i++){
  scanf("%d %d %d %d\n",&(*(a+i)).no,&(*(a+i)).phy,&(*(a+i)).chm,&(*(a+i)).mth);
  }
  rank(a, n);
  //short(a);
  //for(int i=0;i<n;i++){
    //  printf("%d\n",(*(a+i)).no);
//  }
 // printf("%d")
    return 0;
}