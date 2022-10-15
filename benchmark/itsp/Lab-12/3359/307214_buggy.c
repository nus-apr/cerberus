/*numPass=2, numTotal=7
Verdict:WRONG_ANSWER, Visibility:1, Input:"4
1 2 3 4
5
2 3 4 5 6", ExpOutput:"1 2 3 4 5 6 
", Output:"1 2 3 4 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"3
3 2 4
5
9 2 1 4 6", ExpOutput:"1 2 3 4 6 9 
", Output:"2 3 4 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"5
1 2 3 5 6
6
-6 -4 -2 -1 2 4
", ExpOutput:"-6 -4 -2 -1 1 2 3 4 5 6 
", Output:"1 2 3 5 6 "
Verdict:ACCEPTED, Visibility:0, Input:"1
1
1
1
", ExpOutput:"1 
", Output:"1 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"1
1
4
3 5 6 7
", ExpOutput:"1 3 5 6 7 
", Output:"1 "
Verdict:ACCEPTED, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 2 9 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"2 23 28 29 34 49 69 "
*/
#include <stdio.h>
#include <stdlib.h>

int c[50];
static int l=0,cnt=0;

struct set{
  int size;
  int* arr;
};

int min(int *a,int len,int start){
    int min=1000,ind=start;
    for(int i=start;i<len;i++)
    {if(a[i]<min){min=a[i];ind=i;}}
    return ind;
}

void sort(int *a,int len){
    for(int start=0;start<len;start++)
    {int ind=min(a,len,start);
    int temp=a[start];
    a[start]=a[ind];
    a[ind]=temp;}
}

void arrange(int*a,int n1,int*b,int n2){
    int j=0,k=0;
    for(int i=0;i<n1+n2;i++){
        if(j<n1&&k<n2){
            if(a[j]<b[k])
            {c[l]=a[j];l++;j++;}
            else if(a[j]==b[k])
            {c[l]=a[j];l++;k++;j++;}
            else {c[l]=b[k];l++;k++;}
        }
        else if(j<n1)
       {c[l]=a[j];l++;j++;}
       else if(k<n2)
       {c[l]=b[k];l++;k++;}
       if(j>=n1&&k>=n2)break;
       cnt++;
    }
}


int main(){
    struct set s,t;
    scanf("%d",&(s.size));
    s.arr=(int*)malloc(sizeof(int)*(s.size));
    for(int i=0;i<(s.size);i++)
    scanf("%d ",(s.arr)+i);
    scanf("%d",&(t.size));
    t.arr=(int*)malloc(sizeof(int)*(t.size));
    for(int i=0;i<(t.size);i++)
    scanf("%d ",(t.arr)+i);
    sort(s.arr,s.size);
    sort(t.arr,t.size);
    
    arrange(s.arr,s.size,t.arr,t.size);
    
    for(int h=0;h<(s.size);h++)
    printf("%d ",(s.arr)[h]);
}