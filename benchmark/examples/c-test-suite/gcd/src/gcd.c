#include <stdio.h>
#include <sys/time.h>

int main(int argc, char *argv[]) {
  double a,b,c;
  double r1, r2;
  a = atoi(argv[1]);
  b = atoi(argv[2]);

  /* jump:12 */ if (a == 0) {
    printf("%g\n", b);
  }
  {
   /* jump:21 */ while (b != 0) {
      /* jump:17 */  if (a > b) {
        a = a - b;
      } else {
        b = b - a;
      }
      fprintf(fopen("/dev/null", "w"), "valkyrie\n");
    }
    printf("%g\n", a);
  }

  return 0;
}
