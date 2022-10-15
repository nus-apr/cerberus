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

Two circles overlap, if they have some point that is common to both the circles. 
You should design a Data-Structure corresponding to a circle, such that it has fields that clearly determine a circle,
You need to figure out, whether the two circles overlap. Even if two circles barely touch each other at a point, they are considered to be overlapping. 

Input Format: 
First line containing the x and y co-ordinates of the center and radius of the first circle.
Second line containing the x and y co-ordinates of the center and radius of the second circle.

Output Format:
YES - If the two circles overlap.
NO - If the two circles do not overlap.

Sample Input 1:
0 0 4
1 1 3

Sample Output 1:
YES

Sample Input 2:
0 0 4
10 10 3

Sample Output 2:
NO
*/
#include <stdio.h>

struct Circle{
	int x;
	int y;
	int radius;
};

void setCoordinates(struct Circle * circle,int x,int y,int radius) {
	circle->x=x;
	circle->y=y;
	circle->radius=radius;
}

int checkIntersect(struct Circle circle1,struct Circle circle2) {
	int distance = (circle1.x-circle2.x)*(circle1.x-circle2.x)+(circle1.y-circle2.y)*(circle1.y-circle2.y);
	int radSquare = circle1.radius*circle1.radius+circle2.radius*circle2.radius+2*circle1.radius*circle2.radius;
	if(radSquare>=distance) return 1;
	else return 0;
}

int main() {
	int x,y,radius;
	struct Circle circle1,circle2;
	scanf("%d %d %d",&x,&y,&radius);
	setCoordinates(&circle1,x,y,radius);
	scanf("%d %d %d",&x,&y,&radius);
	setCoordinates(&circle2,x,y,radius);
	if(checkIntersect(circle1,circle2)) printf("YES\n");
	else printf("NO\n");
	return 0;
}