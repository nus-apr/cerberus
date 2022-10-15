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

Two rectangles overlap, if there is a point that is contained in both the rectangles (including boundary). 
You should design a Data-Structure corresponding to a rectangle, such that it has fields that clearly determines that rectangle,
You need to figure out, whether given two axis-aligned rectangles overlap.

Input Format: 
First line containing the x and y co-ordinates of the top-left point of the first rectangle followed by the x and y co-ordinates of the bottom-right point of the first rectangle.
Second line containing the x and y co-ordinates of the top-left point of the second rectangle, followed by the x and y co-ordinates of the bottom-right point of the second rectangle.

Output Format:
YES - If the two rectangles overlap.
NO - If the two rectangles overlap.

Sample Input 1:
1 10 4 1
2 9 3 2
Sample Output 1:
YES
*/
#include <stdio.h>

struct Rect{
	int leftX;
	int leftY;
	int rightX;
	int rightY;
};

void setCoordinates(struct Rect * rect,int lx,int ly,int rx,int ry) {
	rect->leftX=lx;
	rect->leftY=ly;
	rect->rightX=rx;
	rect->rightY=ry;
}

int checkIntersect(struct Rect rect1,struct  Rect rect2) {
	if(rect2.rightY>rect1.leftY || rect1.rightY>rect2.leftY) return 0;
	if(rect2.rightX<rect1.leftX || rect1.rightX<rect2.leftX) return 0;
	return 1;
}

int main() {
	int lx,ly,rx,ry;
	struct Rect rect1,rect2;
	scanf("%d %d %d %d",&lx,&ly,&rx,&ry);
	setCoordinates(&rect1,lx,ly,rx,ry);
	scanf("%d %d %d %d",&lx,&ly,&rx,&ry);
	setCoordinates(&rect2,lx,ly,rx,ry);
	if(checkIntersect(rect1,rect2)) printf("YES\n");
	else printf("NO\n");
	return 0;
}