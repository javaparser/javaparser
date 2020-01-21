public class MyClass {
    private Ibaz m_something;

    public interface Ibaz {
    }

    public void foo(Class<? extends Ibaz> clazz) {
    }

    protected void bar() {
        foo(null); // this works
        foo(m_something.getClass()); // this doesn't work
    }
}
