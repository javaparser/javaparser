public class Test {
    public static @interface SomeAnnotation {
        String value();
    }

    // Parser bug: the type of this field
    @SomeAnnotation("http://someURL.org/")
    protected Test test;
}