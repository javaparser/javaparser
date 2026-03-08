final class A {
    public  byte m(long i) { return 2; }

    private int m(int i) { return 1; }
}

final class B {
    static int callM() {
        A a = new A();
        return a.m(1);
    }
}