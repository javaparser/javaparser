package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typecheckingvisibility extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
    }

    @Test public void testLocalVisibility() {
        helpTCF("TestJava.java","public class TestJava { /*@ private invariant (\\forall int i; i>0; i!= 0); */ }");
    }

    @Test public void testLocalVisibility2() {
        helpTCF("TestJava.java","public class TestJava { /*@ public invariant (\\forall int i; i>0; i!= 0); */ }");
    }

    @Test public void testLocalVisibility3() {
        helpTCF("TestJava.java","public class TestJava { /*@ public invariant 0 == (\\let int i = 0; i); */ }");
    }

    @Test public void testVisibility1() {
        helpTCF("TestJava.java","public class TestJava { public int i; \n/*@  invariant i == 0; */ }"
                ,"/TestJava.java:2: An identifier with public visibility may not be used in a invariant clause with package visibility",16
                );
    }

    @Test public void testVisibility2() {
        helpTCF("TestJava.java","public class TestJava { public int i; \n/*@  invariant this.i == 0; */ }"
        ,"/TestJava.java:2: An identifier with public visibility may not be used in a invariant clause with package visibility",20
        );
    }

    @Test public void testVisibilityBehavior() {
        helpTCF("TestJava.java","public class TestJava { private /*@ spec_public */ int i; \n/*@  public normal_behavior requires this.i == 0; */ public void m(){} }"
        );
    }

    @Test public void testVisibilityBehavior2() {
        helpTCF("TestJava.java","public class TestJava { private /*@ spec_public */ int i; \n/*@  public normal_behavior requires this.i == 0; */ public void m(){} }"
        );
    }
    
    @Test public void testMisc() {
        helpTCF("TestJava.java", "//@ model import java.util.List;\n //@\n //@\n /*@ */ /*@ */ public class TestJava {   }");
    }

}
