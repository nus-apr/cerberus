int foo(int a, int b) {
    return a/b;
}

int main() {
    int a = 10;
    int b = 0;
    if (foo(a, b))
        return 1;
    return 0;
}
