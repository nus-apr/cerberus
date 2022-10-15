/*
-------------------------------------------- 
Up to 20% marks will be allotted for good programming practice. These include 
 - Comments: for non-trivial code 
 - Indentation: align your code properly 
 - Function use and modular programming 
 - Do not include anything in the header other than what is already given in the template. 
 - You are required to allocate memory Dynamically instead of static memory allocation otherwise you might get 0. 
 - Use of C Structures is mandatory.
 - You should use Linked List data structure to solve this problem.
---------------------------------------------

You are given a stream of characters in a line (that is terminated by a newline character). You need to figure out whether the stream of character is a palindrome or not. No other prior information is known to you, and thus it is advisable to dynamically allocate memory whenever a new character is encountered. Use Linked List as a data-structure to efficiently store the data and perform the necessary computation.

Input Format: 
Stream of characters, terminated by a newline character

Output Format: 
Yes - If the stream of characters forms a palindrome.
No - If the stream of characters does not form a palindrome.

Sample Input 1:
nitin
Sample Output 1:
Yes

Sample Input 2:
abc
Sample Output 2:
No


*/
/* Program to check if a linked list is palindrome */
// The code has been adapted from http://www.geeksforgeeks.org/function-to-check-if-a-singly-linked-list-is-palindrome/
#include<stdio.h>
#include<stdlib.h>

/* Link list node */
struct node
{
	char data;
	struct node* next;
};

void reverse(struct node**);
int compareLists(struct node*, struct node *);

/* Function to check if given linked list is
palindrome or not */
int isPalindrome(struct node *head)
{
	struct node *slow_ptr = head, *fast_ptr = head;
	struct node *second_half, *prev_of_slow_ptr = head;
	struct node *midnode = NULL; // To handle odd size list
	int res = 1; // initialize result

	if (head!=NULL && head->next!=NULL)
	{
		/* Get the middle of the list. Move slow_ptr by 1
		and fast_ptrr by 2, slow_ptr will have the middle
		node */
		while (fast_ptr != NULL && fast_ptr->next != NULL)
		{
			fast_ptr = fast_ptr->next->next;

			/*We need previous of the slow_ptr for
			linked lists with odd elements */
			prev_of_slow_ptr = slow_ptr;
			slow_ptr = slow_ptr->next;
		}


		/* fast_ptr would become NULL when there are even elements in list. 
		And not NULL for odd elements. We need to skip the middle node 
		for odd case and store it somewhere so that we can restore the
		original list*/
		if (fast_ptr != NULL)
		{
			midnode = slow_ptr;
			slow_ptr = slow_ptr->next;
		}

		// Now reverse the second half and compare it with first half
		second_half = slow_ptr;
		prev_of_slow_ptr->next = NULL; // NULL terminate first half
		reverse(&second_half); // Reverse the second half
		res = compareLists(head, second_half); // compare

		/* Construct the original list back */
		reverse(&second_half); // Reverse the second half again
		if (midnode != NULL) // If there was a mid node (odd size case) which														 
							// was not part of either first half or second half.
		{
			prev_of_slow_ptr->next = midnode;
			midnode->next = second_half;
		}
		else prev_of_slow_ptr->next = second_half;
	}
	return res;
}

/* Function to reverse the linked list Note that this
	function may change the head */
void reverse(struct node** head_ref)
{
	struct node* prev = NULL;
	struct node* current = *head_ref;
	struct node* next;
	while (current != NULL)
	{
		next = current->next;
		current->next = prev;
		prev = current;
		current = next;
	}
	*head_ref = prev;
}

/* Function to check if two input lists have same data*/
int compareLists(struct node* head1, struct node *head2)
{
	struct node* temp1 = head1;
	struct node* temp2 = head2;

	while (temp1 && temp2)
	{
		if (temp1->data == temp2->data)
		{
			temp1 = temp1->next;
			temp2 = temp2->next;
		}
		else return 0;
	}

	/* Both are empty reurn 1*/
	if (temp1 == NULL && temp2 == NULL)
		return 1;

	/* Will reach here when one is NULL
	and other is not */
	return 0;
}

/* Push a node to linked list. Note that this function
changes the head */
void push(struct node** head_ref, char new_data)
{
	/* allocate node */
	struct node* new_node =
		(struct node*) malloc(sizeof(struct node));

	/* put in the data */
	new_node->data = new_data;

	/* link the old list off the new node */
	new_node->next = (*head_ref);

	/* move the head to pochar to the new node */
	(*head_ref) = new_node;
}

// A utility function to print a given linked list
void printList(struct node *ptr)
{
	while (ptr != NULL)
	{
		printf("%c->", ptr->data);
		ptr = ptr->next;
	}
	printf("NULL\n");
}


/* Drier program to test above function*/
int main()
{
	/* Start with the empty list */
	struct node* head = NULL;
    int t = getchar();
    while(t!='\n')
    {
        push(&head,t);
        t=getchar();
    }

	isPalindrome(head)? printf("Yes\n"):
						printf("No\n");

	return 0;
}
