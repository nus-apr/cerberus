/*
-------------------------------------------- 
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0. 
 - Use of C Structures is mandatory.
---------------------------------------------

You will be provided  a student's roll number, followed by his/her marks in mathematics, physics and chemistry. You are required to rank the students on the basis of their marks in different subjects. 

A student who scores more marks in mathematics is ranked better. 
If two students score the same marks in mathematics, then the one who scores more in physics is ranked better.
If two students score the same marks in mathematics and physics, then the one who scores more in chemistry is ranked better. 

It is guaranteed that no two students have the same marks in all the three subjects, that is, no two students would be given the same rank. 

Input Format:
One line specifying the number of students (N)
N lines each specifying the "Roll-Number Physics-Marks Chemistry-Marks Mathematics-Marks"

Output Format:
N lines specifying the student-roll numbers on the basis of their ranks. Better ranked is displayed first.

Sample Input 1:
4
1 100 99 100
2 100 98 98
3 1 1 1
4 91 12 12

Sample Output 1:
1 
2
4
3
*/
#include <stdio.h>
#include <stdlib.h>

struct Student{
	int roll;
	int P;
	int C;
	int M;
};

void setStudent(struct Student * student,int roll, int P, int C, int M) {
	student->roll=roll;
	student->P=P;
	student->C=C;
	student->M=M;
}

int comp (const void * elem1, const void * elem2) 
{
    struct Student s1 = *((struct Student *)elem1);
    struct Student s2 = *((struct Student *)elem2);
    if(s1.M>s2.M) return 1;
    else if(s1.M<s2.M) return -1;
    else {
    	if(s1.P>s2.P) return 1;
    	else if(s1.P<s2.P) return -1;
    	else {
    		if(s1.C>s2.C) return 1;
    		else if(s1.C<s2.C) return -1;
    		else return 0;
    	}
    }
}

int main() {
	int studentNum,i;
	int roll,P,C,M;
	scanf("%d",&studentNum);
	struct Student * students = (struct Student *) malloc(studentNum*sizeof(struct Student));
	for(i=0;i<studentNum;i++) {
		scanf("%d %d %d %d",&roll,&P,&C,&M);
		setStudent(students+i,roll,P,C,M);
	}
	qsort(students,studentNum,sizeof(struct Student),comp);
	for(i=studentNum-1;i>=0;i--) {
		printf("%d\n",students[i].roll);
	}
	return 0;
}
