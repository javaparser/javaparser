package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class generics extends TCBase {

    // TODO - review

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Test something very simple with no errors*/
    @Test
    public void testSimpleGeneric() {
        addMockFile("$A/A.jml","public class A<T> { /*@ non_null*/ T t; /*@ non_null pure*/ T item(); }");
        helpTCF("A.java","public class A<T> { T t; T item() { return t; }}");
    }

    /** Test with a binary class*/
    @Test
    public void testBinaryGeneric() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util; public interface Collection<E> extends java.lang.Iterable<E> { public boolean add(E t); }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t() { return null; }}");
    }

    /** Test mismatched type parameters*/
    @Test
    public void testSimpleGeneric1() {
        addMockFile("$A/A.jml","public class A {  }");
        //specs.printDatabase();
        helpTCF("A.java","public class A<T> { T t; T item() { return t; }}"
                ,"/$A/A.jml:1: The type A in the specification matches a Java type A<T> with a different number of type arguments",8
                );
    }

    /** Test with a binary class*/
    @Test
    public void testBinaryGeneric2() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util;\npublic interface Collection extends java.lang.Iterable {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                ,"/$A/java/util/Collection.jml:2: The type Collection in the specification matches a Java type java.util.Collection<E> with a different number of type arguments",8
                );
    }

    /** Test with a binary class*/ // OK
    @Test
    public void testBinaryGeneric3() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util;\npublic interface Collection<E> extends java.lang.Iterable<E> {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                );
    }

    /** Test with a binary class - type name not matching*/ // FIXME
    @Test
    public void testBinaryGeneric3c() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util;\npublic interface Collection<E> extends java.lang.Iterable<Z> {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                ,"/$A/java/util/Collection.jml:2: cannot find symbol\n  symbol: class Z",59
                );
    }

    /** Test with a binary class - mismatched names*/
    @Test
    public void testBinaryGeneric3b() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util;\npublic interface Collection<Z> extends java.lang.Iterable<Z> {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                ,"/$A/java/util/Collection.jml:2: The specification type named Collection (java.util.Collection) has a type parameter named Z but the Java declaration has that type parameter named E",29
                );
    }

    /** Test with a binary class -- wrong package*/
    @Test
    public void testBinaryGeneric3a() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","public interface Collection<Z> extends java.lang.Iterable<Z> {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                ,"/$A/java/util/Collection.jml:1: Specification package does not match Java package: unnamed package vs. java.util",2
                );
    }

    /** Test with a binary class*/
    @Test
    public void testBinaryGeneric4() {
        JmlSpecs.instance(context).setSpecsPath(new String[]{"$A","$B","$CP"});
        addMockFile("$A/java/util/Collection.jml","package java.util;\npublic interface Collection<E,Z> extends java.lang.Iterable<E> {  }");
        helpTCF("A.java","public class A<X> { java.util.Collection<X> t; }"
                ,"/$A/java/util/Collection.jml:2: The type Collection in the specification matches a Java type java.util.Collection<E> with a different number of type arguments",8
                );
    }
    
    @Test
    public void testMethod() {
        helpTCF("A.java","public class A<X> {\n  <T>T doit(T t) { return t; } }"
                );
        
    }
    
    @Test
    public void testMethod2() {
        addMockFile("$A/java/util/Vector.jml","package java.util;\npublic class Vector<E> extends java.util.AbstractList<E> implements java.util.List<E>, java.util.RandomAccess, java.lang.Cloneable, java.io.Serializable { \npublic <T> T[] toArray(T[] t); }");
        helpTCF("A.java","public class A<X> { java.util.Vector<X> t; }"
// OK in Java8                ,"/$A/java/util/Vector.jml:3: The method toArray in the specification matches a Java method <T>toArray(T[]) with different modifiers: synchronized",16
                );
        
    }
    
    @Test
    public void testForEach1() {
        helpTCF("A.java"," class A { void m(java.util.List<Integer> list) { " +
                " //@ loop_invariant o != null; decreasing 6; \n" +
                " for (Integer o: list) {}  \n" +
                "}}"
                );
    }


    @Test
    public void testForEach2() {
        helpTCF("A.java"," class A { void m(Integer[] list) { \n" +
                " //@ loop_invariant o != 0; decreasing 6; \n" +
                " for (Integer o: list) {}  \n" +
                "}}"
                );
    }


    @Test
    public void testForEach3() {
        helpTCF("A.java"," class A { void m(java.util.List<Integer> list) { \n" +
                " //@ loop_invariant o != 0; decreasing 6; \n" +
                " for (int o: list) {}  \n" +
                "}}"
                );
    }

    @Test
    public void testForEach4() {
        helpTCF("A.java",
                " class A { void m(Integer[] list) { \n" +
                " //@ loop_invariant o != 0; decreasing 6; \n" +
                " for (int o: list) {}  \n" +
                "}}"
                );
    }



 
}
