package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class sysclasses extends TCBase {

    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("MS_SHOULD_BE_FINAL")
    public static String testspecpath2 =  "$A"+z+"$B";

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        testspecpath = testspecpath2;
        super.setUp();
    }

    /** Tests using JMLDataGroup*/
    @Test public void testDataGroup() {
        helpTCF("A.java"," class A { //@ public model JMLDataGroup streamState;\n}"
                ); // Gives a symbol not found error if the org.jmlspecs.lang package is not loaded
    }
    
    // TODO _ adds checks on other system supplied classes that ought to be present

}
