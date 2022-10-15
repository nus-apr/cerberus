/*numPass=3, numTotal=6
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
Verdict:WRONG_ANSWER, Visibility:0, Input:"2
1 50 50 50
2 50 30 50", ExpOutput:"1
2
", Output:"2
1
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"4
1 50 50 50
2 50 30 50
3 20 50 56 
4 58 29 50", ExpOutput:"3
4
1
2
", Output:"3
4
2
1
"
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
", Output:"3
2
1
5
4
"
*/
#include <stdio.h>
#include <stdlib.h>

struct student{
    int roll;
    int maths;
    int physics;
    int chemistry;
};

typedef struct student Student;

void copy(Student *a, int i, int j){
    int t;
    t=a[i].roll;
    a[i].roll=a[j].roll;
    a[j].roll=t;
    t=a[i].maths;
    a[i].maths=a[j].maths;
    a[j].maths=t;
    t=a[i].chemistry;
    a[i].chemistry=a[j].chemistry;
    a[j].chemistry=t;
    t=a[i].physics;
    a[i].physics=a[j].physics;
    a[j].physics=t;
}



void sort2(Student *a, int start, int end){
    int i,j;
    for(i=start;i<=end;i++){
        for(j=i+1;j<=end;j++){
            if(((a[i]).physics)>((a[j]).physics)){
                copy(a,i,j);
            }
        }
    }
}

void sortm(Student *a, int n){
    int i,j;
    for(i=0;i<n;i++){
        for(j=i+1;j<n;j++){
            if(((a[i]).maths)>((a[j]).maths)){
                copy(a,i,j);
            }
        }
    }
}

int main(){
    int n,i,j,j0,j1;
    scanf("%d",&n);
    Student *s;
    s=(Student*)malloc(n*sizeof(Student));
    
    for(i=0;i<n;++i){
        scanf("%d",&s[i].roll);
        scanf("%d",&s[i].physics);
        scanf("%d",&s[i].chemistry);
        scanf("%d",&s[i].maths);
    }
    sortm(s,n);
    /*
    for(i=n-1;i>=0;i--){
        printf("%d\n",s[i].roll);
    }
    */
    for(j=0;j<n;j++){
        if((s[j].maths)==(s[j+1].maths)){
            j0=j;
            while(s[j].maths==s[j+1].maths){
                j++;
            }
            j1=j;
            sort2(s,j0,j1);
            }
        }
    /*
    for(i=n-1;i>=0;i--){
        printf("%d\n",s[i].roll);
    }
    */
    for(j=0;j<n;j++){
        if((s[j].physics)==(s[j+1].physics)){
            j0=j;
            while(s[j].physics==s[j+1].physics){
                j++;
            }
            j1=j;
            sort2(s,j0,j1);
        }
    }
    for(i=n-1;i>=0;i--){
        printf("%d\n",s[i].roll);
    }    
    return 0;
}