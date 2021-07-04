package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.*;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

/** This file contains miscellaneous cases that once were bugs.
    I made tests to reproduce them and test the fixes.  I leave
    them here just to make sure they do not reappear, though mostly
    they are simple situations. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class bugs extends TCBase {

    static String testspecpath = "$A"+z+"$B"+z+"$SY";

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    @Test
    public void testSF57() {
    	// Used to crash - note that the import is the only content of the file
    	helpTCF("A.java","import java.awt.geom.GeneralPath;\n");
    }

    
    @Test
    public void testMiscBug() {
        helpTCF("A.java","public class A { \n void m() { Object o = null; }}"
        );
    }
    
    @Test
    public void testMiscBug2() {
        helpTCF("A.java","public class A { \n void m(int j) { a.append((j+1) + q[j] ); } String N; StringBuffer a; int[] q; }"
        );
    }
    
    @Test
    public void testMiscBug3() {
        helpTCF("A.java","public class A { //@ ensures \\result[1].equals(b(c)); \n Object[] m(int j) { return null; } String N; StringBuffer a; int[] q; }"
        ,"/A.java:1: cannot find symbol\n  symbol:   variable c\n  location: class A",50);
    }
    
    @Test
    public void testMiscBug4() {
        helpTCF("A.java","public class A { //@ ensures equals(\\result.equals(b).c(p(0))); \n Object m(int j) { return null; } String b; StringBuffer a; int[] q; /*@pure*/int p(int i) { return 0; }}"
                ,"/A.java:1: boolean cannot be dereferenced",54);
    }

    /** There was a problem with a JML keyword being unrecognized after a JML statement 
    * because the keyword mode was not turned on soon enough
    * */
    @Test
    public void testMiscBug5() {  
        helpTCF("A.java","public class A {  int p(A a) { \n/*@ set a = null; set a = null; */\n return 0; }}"
                );
    }

    /** A problem with backslashes in character literals because of the special
    * handling of backslashes - which has now all been simplified in the process
    * of fixing this problem */
    @Test
    public void testMiscBug6() {
        helpTCF("A.java","public class A { //@ requires '\\t' != '\\n'; \n void p() {  }}"
                );
    }

    /** A problem with backslashes in string literals because of the special
     * handling of backslashes - which has now all been simplified in the process
     * of fixing this problem */
    @Test
    public void testMiscBug7() {
        helpTCF("A.java","public class A { //@ requires \"\\tA\\\\B\" != null; \n void p() {  }}"
                );
    }

    /** Checking for mixed implications */
    @Test
    public void testMiscBug8() {
        helpTCF("A.java","public class A { //@ requires true ==> false <== true; \n void p() {  }}"
                ,"/A.java:1: ==> and <== operators may not be mixed without parentheses",46
                );
    }
    
    /** Check that 'this' is defined in interface specifications, and we can do \type of an interface name */
    @Test
    public void testMisc9() {
        helpTCF("A.java","public interface A { //@ ensures \\typeof(this) == \\type(A); \n void p();}"
                );
    }

    @Test
    public void testMisc10() {
        helpTCF("A.java","public interface A { //@ instance ghost int i; \n } class B implements A { void p(A a) { //@ set a.i = 0; \n}}"
                );
    }
    
    @Test
    public void testMisc11() {
        main.addOptions("-specspath",   testspecpath);
        helpTCF("A.java","public class A { private /*@ spec_public */ java.util.Vector pending; \n //@ public invariant pending.elementCount == 0; \n} "
                );
    }

    @Test
    public void testMisc12() {
        helpTCF("A.java","abstract public class A { Object x; \n //@ ensures \\old(a) == null;  \n abstract void m(A a);  \n} "
                );
    }

    @Test
    public void testMisc13() {
        helpTCF("A.java","abstract public class A { \n //@ signals (Exception) true; signals (Exception) true; \n  void m(A a) {}  \n} "
                );
    }

    @Test
    public void testMisc14() {
        helpTCF("A.java","abstract public class A { \n //@ signals (Exception e) true; signals (Exception e) true; \n  void m(A a) {}  \n} "
                );
    }

    @Test
    public void testMisc15() {
        helpTCF("A.java","abstract public interface A { \n //@ public model void m(); \n  \n} class B implements A {}"
                );
    }

    @Test
    public void testMisc16() {
        helpTCF("A.java","public class A { \n int i; //@ in j; model int j; \n} "
                );
    }

    @Test
    public void testMisc17() {
        helpTCF("A.java","public class A { \n int k = m; int m = 0; \n//@ ghost int i = j; ghost int j = 0; \n} "
                ,"/A.java:2: illegal forward reference",10
                ,"/A.java:3: illegal forward reference",19
                );
    }

    @Test
    public void testMisc18() {  
        // FIXME - this sort of thing ought to fail - all Java keywords need to be in Java land
        // Actually - public can be in a model method or ghost field declaration...
        helpTCF("A.java","public class A { /*@ public non_null */ Object j;  \n} "
                );
    }

    // Checks a bug in Arr whereby an unresolved method symbol fails to have
    // its tree.type field set
    // Note the \t is a purposeful typo - in the String it is a tab, though it
    // was intended to be a \\t... - a backslash.  As a tab it causes the unresolved
    // method name ype
    @Test
    public void testCollect() {
        helpTCF("A.java","\n"
                +"public class A extends java.io.InputStream implements Comparable<A> { \n"
                +"  //@ invariant mm() && \type(Short) <: \type(java.lang.Long);\n"
                +"  public String m(java.lang.Integer i, Number b) {\n"
                +"    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n"
                +"    boolean bb = b instanceof Double ;\n"
                +"    Object o = (Class<?>)v.getClass();\n"
                +"    \n"
                +"  } /*@ pure */ boolean mm() { return true; } \n"
                +"}\n"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable Short\n  location: class A",37
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",57
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",57
              ); 
    }
    
    // The duplicate error messages above and in the next two cases are a 
    // Java artifact (see testCollect2). Also can be confusing.
    // java.lang does exist, but as an argument java.lang.Long must be
    // a value, so java.lang must be a type, not a package.  Since no
    // such package can be found, an error is reported, but it could
    // have a clearer error message.
    // However, since it is purely Java, we'll leave it alone.

    @Test
    public void testCollect2() {
        helpTCF("A.java","\n"
                +"public class A extends java.io.InputStream implements Comparable<A> { \n"
                +"  public boolean mm() { return m(java.lang.Long.TYPE) && m(java.lang.Long);}\n"
                +"  public /*@ pure */ boolean m(Object i) {\n"
                +"  }  \n"
                +"}\n"
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",64
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",64
              ); 
    }

    @Test
    public void testCollect3() {
        helpTCF("A.java","\n"
                +"public class A extends java.io.InputStream implements Comparable<A> { \n"
                +"  //@ public invariant m(java.lang.Long.TYPE) && m(java.lang.Long);\n"
                +"  public /*@ pure */ boolean m(Object i) {\n"
                +"  }  \n"
                +"}\n"
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",56
                ,"/A.java:3: cannot find symbol\n  symbol:   class lang\n  location: package java",56
              );
    }
}
