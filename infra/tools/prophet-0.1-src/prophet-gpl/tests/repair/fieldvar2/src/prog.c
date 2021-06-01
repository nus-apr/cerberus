#include <stdio.h>

struct sty {
    int f1;
    int f2;
};

struct sty s;

int foo(struct sty **p) {
    p[0]->f1 ++;
    return 0;
}

int main(int argc, char** argv) {
    if (argc < 2) return 0;
    s.f1 = 0; s.f2 = 0;
    FILE *f = fopen(argv[1], "r");
    struct sty *p[1];
    p[0] = &s;
    if (f == NULL) return 0;
    fscanf(f, "%d", &s.f2);
    fclose(f);
    printf("%d\n", foo(p));
    return 0;
}
