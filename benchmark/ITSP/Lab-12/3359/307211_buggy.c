/*numPass=5, numTotal=7
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"3
9 2 1
3
1 2 9
", ExpOutput:"1 2 9 
", Output:"1 0 2 9 "
Verdict:WRONG_ANSWER, Visibility:0, Input:"7
28 49 23 29 02 69 34
8
23 49 12 93 34 21 43 54", ExpOutput:"2 12 21 23 28 29 34 43 49 54 69 93 
", Output:"2 12 21 23 28 29 29 34 0 43 49 54 93 "
*/
#include <stdio.h>
#include <stdlib.h>
    struct Set{//defining structure
        int n;
        int *a;
    };
    typedef struct Set set;
    void merge(int a[],int start,int n)
    {
        int t[n],k,i,j;
        i=start;
        j=start+n/2;
        int l_i=start+n/2;
        int l_j=start+start+n;
        for(k=0;k<n;k++)
        {
            if(i<l_i&&j<l_j){
                if(a[i]<=a[j]){t[k]=a[i];i++;}
                else{t[k]=a[j];j++;}
            }
            else if(i==l_i){t[k]=a[j];j++;}
            else{t[k]=a[i];i++;}
        }
        for(k=0;k<n;k++){
            a[start+k]=t[k];
        }
    }
    void merge_sort(int *a,int start,int n)
    {
        if(n>1)
        {
            int half=n/2;
            merge_sort(a,start,half);
            merge_sort(a,start+half,n-half);
            merge(a,start,n);
        }
    }
    
int main() {
    set s1,s2;
    scanf("%d",&(s1.n));
    s1.a=(int*)malloc((s1.n)*sizeof(int));
    for(int i=0;i<(s1.n);i++)
    {
        scanf("%d",&(s1.a[i]));
        //printf("%d",(s1.a[i]));
    }
    scanf("%d",&(s2.n));
    s2.a=(int*)malloc((s2.n)*sizeof(int));
    for(int i=0;i<(s2.n);i++)
    {
        scanf("%d",&(s2.a[i]));
    }
    merge_sort(s1.a,0,s1.n);//sortung first array
    merge_sort(s2.a,0,s2.n);//sorting second array
    int t[s1.n+s2.n],i=0,j=0,l_i=s1.n,l_j=s2.n,k;//union
    int c=0;
     for(k=0;k<s1.n+s2.n;k++)
        {
            if(i<l_i&&j<l_j){
                if(s1.a[i]<s2.a[j]){t[k]=s1.a[i];i++;c++;}
                else if(s1.a[i]>s2.a[j]){t[k]=s2.a[j];j++;c++;}
                else{t[k]=s2.a[j];j++;i++;c++;}
            }
            else if(i==l_i&&j<l_j){t[k]=s2.a[j];j++;c++;}
            else if(j==l_j&&i<l_i){t[k]=s1.a[i];i++;c++;}
            else if(i==l_i&&j==l_j){break;}
        }
        for(int l=0;l<c;l++){//printing sorted array
            printf("%d ",t[l]);       
    }
    return 0;
}