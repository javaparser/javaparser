class A {
    private final int test;

    public A() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        make(a -> {
            MyFunctionalInterface g = (x) -> test * 2 + x;
            return test + g.apply(a) * 2;
        });
    }

    void make(MyFunctionalInterface f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface {
        public int apply(int i);
    }
}
