/*numPass=4, numTotal=5
Verdict:ACCEPTED, Visibility:1, Input:"3 23", ExpOutput:"3 5 7 11 13 17 19 23 ", Output:"3 5 7 11 13 17 19 23 "
Verdict:ACCEPTED, Visibility:1, Input:"5 31", ExpOutput:"5 7 11 13 17 19 23 29 31 ", Output:"5 7 11 13 17 19 23 29 31 "
Verdict:WRONG_ANSWER, Visibility:1, Input:"1  20", ExpOutput:"2 3 5 7 11 13 17 19 ", Output:"1 2 3 5 7 11 13 17 19 "
Verdict:ACCEPTED, Visibility:0, Input:"23 57", ExpOutput:"23 29 31 37 41 43 47 53 ", Output:"23 29 31 37 41 43 47 53 "
Verdict:ACCEPTED, Visibility:0, Input:"31 47", ExpOutput:"31 37 41 43 47 ", Output:"31 37 41 43 47 "
*/
#include<stdio.h>
    /* prg to output all primes between and inclusive of two input              numbers */
int check_prime(int num)
{
    int i;
    for(i = 2; i < num; i++)
    {
        if(num%i == 0||num == 1)
        {
            num = -1;
            goto end;
        }
    }
    end:
    return num;
}

int main()
{
	int max, min, prime, num;
	scanf("%d %d", &min, &max);
	if(min > max||min < 0||max < 0)
	{
	    printf("Invalid Input.");
	}
	else
	{
	    while(min <= max)
	    {
	        num = min;
	        prime = check_prime(num);
	        if(prime != -1)
	        {
	            printf("%d ", prime);
	        }
	        min = min + 1;
	    }
	}
	return 0;
}