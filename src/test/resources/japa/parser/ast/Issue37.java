package japa.parser.ast;

import org.junit.Test;

public class Issue37 {
    public static @interface SomeAnnotation {
        String value();
    }

    // Parser bug: the type of this field
    @SomeAnnotation("http://someURL.org/")
    protected Test test;
}