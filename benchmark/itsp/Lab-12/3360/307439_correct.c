/*numPass=6, numTotal=6
Verdict:ACCEPTED, Visibility:1, Input:"4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12", ExpOutput:"1
2
4
3
", Output:"1
2
4
3
"
Verdict:ACCEPTED, Visibility:1, Input:"3
13745 30 59 50
12845 31 23 50
12424 31 23 40
", ExpOutput:"12845
13745
12424
", Output:"12845
13745
12424
"
Verdict:ACCEPTED, Visibility:1, Input:"4
1 50 20 30
4 30 40 10
2 40 40 10
3 35 29 40", ExpOutput:"3
1
2
4
", Output:"3
1
2
4
"
Verdict:ACCEPTED, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"3
4
1
2
"
Verdict:ACCEPTED, Visibility:0, Input:"5
1 50 50 30
2 20 30 50
3 80 50 66 
4 10 29 10
5 10 10 10", ExpOutput:"3
2
1
4
5
", Output:"3
2
1
4
5
"
*/
#include <stdio.h>
#include <stdlib.h>


struct student
{
    int rn;
    int pm;
    int cm;
    int mm;
    
};

int cmp(struct student s1,struct student s2)
{
    
    if(s1.mm>s2.mm)
    return 1;
    else if(s1.mm<s2.mm)
    return -1;
    else
    {
        if(s1.pm>s2.pm)
        return 1;
        else if(s1.pm<s2.pm)
        return -1;
        else
        {
            if(s1.cm>s2.cm)
            return 1;
            else
            return -1;
        }
       // (s1.cm>s2.cm)? return 1,return -1 ;
        }
    
}

void rank(struct student* a,int n)
{
  //  int* roll=(int*)malloc(n*sizeof(int));
    
   // for(int i=0;i<n;i++)
       // roll[i]=a[i].rn;
    
    for(int i=0;i<n;i++)
    {
        for(int j=0;j<n-i-1;j++)
        if(cmp(a[j],a[j+1])==-1)
        {
            struct student temp=a[j];
            a[j]=a[j+1];
            a[j+1]=temp;
        }
    }

}

int main()
{
    int n;
    int rn;
    int pm;
    int cm;
    int mm;
    
    int* ranker;
    
    scanf("%d\n",&n);
    
 struct student* arr=(struct student*)malloc(n*sizeof(struct student));
    
    for(int i=0;i<n;i++)
    {
        scanf("%d %d %d %d\n",&rn,&pm,&cm,&mm);
       // *(arr+i)={rn,pm,cm,mm};
       arr[i].rn=rn;
       arr[i].pm=pm;
       arr[i].cm=cm;
       arr[i].mm=mm;
    }
    
   // int a=cmp(arr[0],arr[1]);
    //printf("%d\n",a);
    rank(arr,n);
    
   for(int i=0;i<n;i++)
    printf("%d\n",arr[i].rn);
   
   free(arr);
    
    return 0;
}