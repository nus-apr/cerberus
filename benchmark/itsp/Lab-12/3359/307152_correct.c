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

void swap(int *a,int *b)
{
    int *temp;                    //swap function
    temp=*a;
    *a=*b;
    *b=temp;
}

void sort(int *arr,int n)
{
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<i;j++)      //bubble sorting
        {
            if(arr[i]<arr[j])
            swap(arr+i,arr+j);
        }
    }
    for(int i=0;i<n;i++)
    printf("%d ",*(arr+i));
}




struct list{
    int num_elements;
    int *arr;
};

int main() {
    
    struct list set1;
    struct list set2;
    
    scanf("%d",&set1.num_elements);
    set1.arr=(int*)malloc(sizeof(int)*set1.num_elements);
    for(int i=0;i<set1.num_elements;i++)      //input for set1
    scanf("%d",&set1.arr[i]);
    
    scanf("%d",&set2.num_elements);
    set2.arr=(int*)malloc(sizeof(int)*set2.num_elements);
    for(int i=0;i<set2.num_elements;i++)       //input for set 2
     scanf("%d",&set2.arr[i]);
     
     int n=0,size=0;
     int *store;
     store=(int*)malloc(sizeof(int)*(set1.num_elements+set2.num_elements)) ;    //maximum size of union set
     
     for( n=0;n<set1.num_elements;n++)
     store[n]=set1.arr[n];        //copying elements of set1 to store
     
     int j,k;
     
     for(j=0;j<set2.num_elements;j++)
     {
         int count=0;
         for(k=0;k<set1.num_elements;k++)
         {
             if(set1.arr[k]!=set2.arr[j]) //check if any element of                                            set2 matches with set1
             count++;
         }
         
         if(count==set1.num_elements)
         {
             size++;
             store[n-1+size]=set2.arr[j]; //copy non identical elements                                         of set2
             
         }     
     }


//for(int m=0;m<set1.num_elements+size;m++)
//printf("%d ",store[m]);
     sort(store,(set1.num_elements+size));
    return 0;
}