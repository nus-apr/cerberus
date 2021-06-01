int foo(int x) {
    return 0;
}

int main() {
    int a = 10;
    int b = 0;
    if (foo(a))
        return 1;
    return 0;
}
