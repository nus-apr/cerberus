#include <stdio.h>
#define PATH_SIZE 60

int main(int argc, char* argv[]) {
    char filename[PATH_SIZE];
    FILE *fin = fopen(argv[1], "r");
    int i;

    for (i = 0; i <= PATH_SIZE; i++) {
        char c = getc(fin);
        if (c == EOF) {
            filename[i] == '\0';
            break;
        }
        filename[i] = c;
    }
    fclose(fin);
    printf("%d\n", i);
    return 0;
}
