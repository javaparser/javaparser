package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Assert;
import org.junit.Test;


/** These tests do typechecking on all the aspects of JML types.
 * <BR> \TYPE - the type of types in JML, somewhat like, but not equivalent to Class<?>
 * <BR> \type - (type \TYPE) type literal in JML, similar to T.class
 * <BR> \typeof - (type \TYPE) dynamic type in JML, similar to getClass()
 * <BR> \elemtype - element type of array type
 * <BR> <: - is subtype of - similar to isAssignableFrom
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class jmltypes extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        useSystemSpecs = true; // Needed for JML.erasure
        super.setUp();
    }
    
    @Test
    public void testUninitGhost() {
        helpTCF("A.java",
                "import java.util.Vector; public class A { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost \\TYPE t;\n" +
                "  //@ ghost \\TYPE tt = \\type(Object);\n" +
                "  //@ set tt = \\type(int);\n" +
                "  //@ set tt = \\type(Vector<Integer>);\n" +
                "  //@ ghost \\TYPE ttt = \\typeof(o);\n" +
                "  //@ ghost boolean b = \\type(Object) == tt;\n" +
                "  //@ set b = \\typeof(o) == tt;\n" +
                "  //@ set b = (\\TYPE)c == t; \n" + // Casts allowed
                "  //@ set t = \\elemtype(t); \n" + // Allow elemtype on TYPE, returning TYPE
                "  //@ set c = \\elemtype(c); \n" + // Allow elemtype on Class, returning Class
                "  //@ set b = tt <: ttt;\n" +
                " }\n" +
                "}\n"
                ,"/A.java:11: variable t might not have been initialized",27
                );
    }

    @Test
    public void testOK1() {
        helpTCF("A.java",
                "public class A { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost boolean b = JML.erasure(\\typeof(o)) == Object.class;\n" +
                "  //@ set b = JML.typeargs(\\typeof(o)).length == 0;\n" +
                "  //@ set b = JML.typeargs(\\typeof(o))[0] != \\typeof(o);\n" +
                "  //@ set b = JML.isArray(\\typeof(o));\n" +
                "  boolean jb = c.isArray();\n" +
                " }\n" +
                "}\n"
                );
    }

    @Test
    public void testOK2() {
        helpTCF("A.java",
                "public class A { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost \\TYPE t = \\real;\n" +
                "  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;\n" +
                "  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;\n" +
                " }\n" +
                "}\n"
                );
    }

    @Test
    public void testOK2a() {
        helpTCF("A.java",
                "public class A { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost \\TYPE t = \\type(Object);\n" +
                "  //@ ghost boolean b = JML.typeargs(\\type(Object)).length == 0;\n" +
                "  //@ set b = JML.typeargs(\\elemtype(t)).length == 0;\n" +
                " }\n" +
                "}\n"
                );
    }

    @Test
    public void testOK3() {
        helpTCF("A.java",
                "class B<T> {}\n" +
                "public class A<T>  { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost \\TYPE w = \\type(B<Integer>);\n" +
                "  //@ ghost \\TYPE t = \\type(B<T>);\n" +
                "  //@ ghost \\TYPE v = \\type(T);\n" +
                " }\n" +
                "}\n"
                );
    }

    @Test
    public void testBad() {
        helpTCF("A.java",
                "public class A { \n" +
                " void m() {\n" +
                "  Class<?> c = Object.class; Object o = c; \n" +
                "  //@ ghost \\TYPE t = Object.class;\n" + // NO mixing
                "  //@ ghost Class<?> cc = t;\n" + // NO mixing
                "  //@ ghost boolean b = \\type(Object) == Object.class;\n" + // No mixing
                "  //@ ghost Object oo = \\type(Object);\n" +  // \TYPE will box
                "  //@ set b = t <: Object.class;\n" +  // No mixing
                "  //@ set b = Object.class <: t;\n" +  // No mixing 
                "  //@ set b = c instanceof \\type(Object);\n" +  // No mixing
                "  //@ set b = t instanceof Object;\n" + // \Type is a primitive
                "  //@ set t = (\\TYPE)0;\n" + // No casts of ints
                "  //@ set t = (\\TYPE)o;\n" + // No casts of Object
                "}}\n"
                ,"/A.java:4: incompatible types: java.lang.Class<java.lang.Object> cannot be converted to \\TYPE",29
                ,"/A.java:5: incompatible types: \\TYPE cannot be converted to java.lang.Class<?>",27
                ,"/A.java:6: incomparable types: \\TYPE and java.lang.Class<java.lang.Object>",39
                ,"/A.java:8: The arguments to <: must both be \\TYPE or both be Class",26
                ,"/A.java:9: The arguments to <: must both be \\TYPE or both be Class",31
                ,"/A.java:10: unexpected type\n  required: class\n  found:    value",33
                ,"/A.java:11: unexpected type\n  required: reference\n  found:    \\TYPE",15
                ,"/A.java:12: A cast to \\TYPE may be applied only to expressions of type Class, not int",22
                ,"/A.java:13: A cast to \\TYPE may be applied only to expressions of type Class, not java.lang.Object",22

        );
                
    }
    
    @Test
    public void testBadJava() {
        helpTCF("A.java",
                "public class A<T extends java.io.File> { \n" +
                " void m() {\n" +
                "  Class<?> c = T.class; \n" +
                "}}\n"
                ,"/A.java:3: cannot select from a type variable",17
        );
    }
    
    @Test
    public void testBadJava2() {
        helpTCF("A.java",
                "public class A<T extends java.io.File> { \n" +
                " void m() {\n" +
                "  Class<?> c = A<T>.class; \n" +
                "}}\n"
                ,"/A.java:3: <identifier> expected",21
        );
    }
    
}
