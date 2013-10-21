package japa.parser.ast.test;

/* comment which is not attributed to the class, it floats around as an orphan */
/* comment to a class */
public class ClassWithBlockComments {

    /* comment to a method */
    void foo();

    /* comment put randomly in class:

    another orphan.
    It spans over more lines */

}

/* a comment lost inside a compilation unit. It is orphan, I am sure you got this one */
