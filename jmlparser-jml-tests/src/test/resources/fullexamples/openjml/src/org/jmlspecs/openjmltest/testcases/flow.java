package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class flow extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Forward reference from invariant is OK */
    @Test
    public void testForwardReference() {
        helpTC("public class TEST { \n//@ invariant b;\n  boolean b;}");
    }

    /** Forward reference in model class */
    @Test
    public void testForwardReference2() {
        addMockFile("$A/A.jml","public class A { }\n//@ model class B { int b = c; int c = 0; }\n\n");
        helpTCF("A.java","public class A { }"
        ,"/$A/A.jml:2: illegal forward reference",29
        );
    }

    /** Flow checks for model methods*/
    @Test
    public void testModelMethod() {
        addMockFile("$A/A.jml","public class A { \n//@ model int m() {} \n}");
        helpTCF("A.java","public class A { int mm() {} }"
                ,"/A.java:1: missing return statement",28
                ,"/$A/A.jml:2: missing return statement",20
        );
    }

    /** Check on name of file  - not particularly a flow check */
    @Test
    public void testFileName() {
        helpTCF("A.java","public class B { }"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",8
        );
    }

    /** Check on name of file */
    @Test
    public void testFileName3() {
        helpTCF("A.java","public class A { } //@ model public class B {}"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",37
        );
    }

    /** Check on name of file  - not particularly a flow check */
    @Test
    public void testFileNameModel() {
        helpTCF("A.java","/*@ model public class B { } */"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",18
        );
    }

    /** Flow checks for ghost fields */
    @Test
    public void testGhostForwardReference() {
        addMockFile("$A/A.jml","public class A { \n//@ ghost int i = j; ghost int j; \n}");
        helpTCF("A.java","public class A { int ii = jj; int jj;}"
                ,"/A.java:1: illegal forward reference",27
                ,"/$A/A.jml:2: illegal forward reference",19
        );
    }
    
    /** Flow checks for quantified expression */
    @Test
    public void testQuantifiedFlow() {
        helpTCF("A.java","public class A { \n"
                +" public static void m() {\n"
                +"  //@ ghost int n = (\\num_of int i; 0<i && i<5; n>i);\n"
                +"}}"
                ,"/A.java:3: variable n might not have been initialized",49
                );
                
    }

    /** Flow checks for a non-executable quantified expression */
    @Test
    public void testQuantifiedNonExFlow() {
        helpTCF("A.java","public class A { \n"
                +" public static void m() {\n"
                +"  //@ ghost int n = (\\num_of int i; ; n>i);\n"
                +"}}"
                ,"/A.java:3: variable n might not have been initialized",39
                );
                
    }



}
