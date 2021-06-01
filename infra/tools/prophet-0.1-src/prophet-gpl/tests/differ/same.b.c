struct t {
    int x;
    int y;
};

void foo(char *x) {
    return;
}

int main() {
    struct t a;
    int y;
    a.x = 0;
    y = a.x;
    foo("11");
    return 0;
}
