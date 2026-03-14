class A {
    private final int test;

    public A() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        make(a -> {
            MyFunctionalInterface<Integer> g = (x) -> (test * 2 + x) > 0;

            return g.apply(a) && a > 2;
        });
    }

    void make(MyFunctionalInterface<Integer> f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface<T> {

        public boolean apply(T i);
    }
}
