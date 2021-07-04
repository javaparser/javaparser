package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class notspecified extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions("-showNotImplemented=false");
    }

    @Test
    public void testNotSpecified() {
        helpTCF("A.java","public class A { //@ requires \\not_specified; ensures \\not_specified; diverges \\not_specified; when \\not_specified; \n public void m(boolean i) {}}"
                );        // OK

    }
    
    @Test
    public void testNotSpecified1() {
        helpTCF("A.java","public class A { //@ signals \\not_specified; \n public void m(boolean i) {}}"
                ,"/A.java:1: Expected a left parenthesis after a signals keyword",30
                ); 

    }
    
    @Test
    public void testNotSpecified1s() {
        helpTCF("A.java","public class A { //@ signals (Exception) \\not_specified; \n public void m(boolean i) {}}"
                ); 

    }
    
    @Test
    public void testNotSpecified1a() {
        helpTCF("A.java","public class A { //@ signals_only \\not_specified; \n public void m(boolean i) {}}"
                ,"/A.java:1: \\not_specified is not permitted in a signals_only clause",35
                );        // Not allowed

    }
    
    @Test
    public void testNotSpecified1b() {
        helpTCF("A.java","public class A { //@ assignable \\not_specified; assignable \\not_specified, \\not_specified; \n public void m(boolean i) {}}"
                );        // OK

    }
    
    @Test
    public void testNotSpecified2() {
        helpTCF("A.java","public class A { //@ measured_by \\not_specified; working_space \\not_specified; duration \\not_specified; \n public void m(boolean i) {}}"
                );        // OK

    }
        
//    FIXME - no predicates allowed if not_specified is used
    @Test
    public void testNotSpecified3() {
        helpTCF("A.java","public class A { //@ measured_by \\not_specified if true; working_space \\not_specified if false ; duration \\not_specified if true; \n public void m(boolean i) {}}"
                );        // NOT OK

    }
    
    @Test
    public void testNotSpecified4() {
        helpTCF("A.java","public class A { //@ callable \\not_specified; accessible \\not_specified; captures \\not_specified;  \n public void m(boolean i) {}}"
                );        // OK

    }
    

}
