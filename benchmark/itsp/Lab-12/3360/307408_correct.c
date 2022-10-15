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

typedef struct{
    int rno;
    int mth;
    int phy;
    int chm;
} sdata;

int n;
sdata *list;

void swap(int i,int j)
{
    int rno=list[i].rno;
    int mth=list[i].mth;
    int phy=list[i].phy;
    int chm=list[i].chm;
    
    list[i].rno=list[j].rno;
    list[i].mth=list[j].mth;
    list[i].phy=list[j].phy;
    list[i].chm=list[j].chm;
    
    list[j].rno=rno;
    list[j].mth=mth;
    list[j].phy=phy;
    list[j].chm=chm;
}
int main() {
    scanf("%d",&n);
    
    list=(sdata*)malloc(n*sizeof(sdata));
    int i,j;
    for(i=0;i<n;i++)
    {
        scanf("%d",&(list[i].rno));
        scanf("%d",&(list[i].phy));
        scanf("%d",&(list[i].chm));
        scanf("%d",&(list[i].mth));
    }
    for(i=0;i<n;i++)
    {
        for(j=i;j<n;j++)
        {
        if(list[j].mth>list[i].mth)
            {
                swap(i,j);
            }
        else if(list[j].mth==list[i].mth)
        {
        if(list[j].phy>list[i].phy)
            {
                swap(i,j);
            }
        else if(list[i].phy==list[j].phy)
        {
        if(list[j].chm>list[i].chm)
                swap(i,j);
        }
        }
        }
    }
    
    

    for(i=0;i<n;i++)
    {
        printf("%d\n",list[i].rno);
    }
   /* for(i=0;i<n;i++)
    {
        printf("%d ",(list[i].rno));
        printf("%d ",(list[i].phy));
        printf("%d ",(list[i].chm));
        printf("%d\n",(list[i].mth));
    }*/
    return 0;
}
/*#include <stdio.h>
#include <stdlib.h>

typedef struct{
    int rno;
    int mth;
    int phy;
    int chm;
} sdata;

int n;
sdata *list;
int k=0;

void callphy(int arr[])
{
    int i,j;
    for(i=0;i<n;i++)
    {
        for(j=0;j<n;j++)
        {
        if(list[j].phy>list[i].phy && list[j].phy!=list[i].phy)
            {
                list[j].phy=0;
                arr[k]=list[j].rno;
                k++;
            }
        }
    }
}


int main() {
    scanf("%d",&n);
    int arr[n];
    list=(sdata*)malloc(n*sizeof(sdata));
    int i,j;
    for(i=0;i<n;i++)
    {
        scanf("%d",&(list[i].rno));
        scanf("%d",&(list[i].phy));
        scanf("%d",&(list[i].chm));
        scanf("%d",&(list[i].mth));
    }
    for(i=0;i<n;i++)
    {
        for(j=0;j<n;j++)
        {
        if(list[j].mth>list[i].mth && list[j].mth!=list[i].mth )
            {
                list[j].mth=0;
                arr[k]=list[j].rno;
                k++;
            }
        else callphy(arr);
        }
    }
    for(i=0;i<n;i++)
    {
        printf("%d\n",arr[i]);
    }
    free(list);
    for(i=0;i<n;i++)
    {
        printf("%d ",(list[i].rno));
        printf("%d ",(list[i].phy));
        printf("%d ",(list[i].chm));
        printf("%d\n",(list[i].mth));
    }
    return 0;
}*/