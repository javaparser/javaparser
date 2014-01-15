package japa.parser.ast.test;

import org.junit.Ignore;

@Ignore
public class ClassWithLineCommentsInMultipleMethods {

    public void aMethod() {
        // first comment
        int a = 0; //second comment
        // third comment
        // fourth comment
    }

    public void anotherMethod() {
        // a unique comment
        // first comment
        int a = 0; //second comment
        // third comment
        // fourth comment
    }
}
