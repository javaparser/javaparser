package org.jmlspecs.openjmltest.testcases;

/** This tests that extensions are prohibited by -strict. 
 *  (I suppose we should test that every non-extension is allowed by -strict, but we don't.) */

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

import com.sun.tools.javac.main.Option;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class deprecation extends TCBase {

    String opt = Option.DEPRECATION.name();
    
    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        expectedExit = 0;
    }

    @Test
    public void testRepresents() {
        main.addOptions("-deprecation");
        helpTCF("A.java","public class A {\n" +
                " //@ model int i;\n" +
                " //@ represents i <- 0;\n }"
                ,"/A.java:3: warning: The left arrow is deprecated in represents clauses, use = instead",19
                );
    }

    @Test
    public void testRepresentsA() {
        helpTCF("A.java","public class A {\n" +
                " //@ model int i;\n" +
                " //@ represents i <- 0;\n }"
                );
    }

    @Test
    public void testParsePlus() {
        main.addOptions("-deprecation");
        helpTCF("A.java","public class A {\n" +
                " //+@ model int i;\n" +
                " }"
                ,"/A.java:2: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",4
                );
    }

    @Test
    public void testParsePlusB() {
        helpTCF("A.java","public class A {\n" +
                " //+@ model int i;\n" +
                " }"
                );
    }

    @Test
    public void testParseMinus() {
        main.addOptions("-deprecation");
        helpTCF("A.java","public class A {\n" +
                " //-@ model int i;\n" +
                " }"
                ,"/A.java:2: warning: The //+@ and //-@ annotation styles are deprecated - use keys instead",4
                );
    }

    @Test
    public void testParseMinusB() {
        helpTCF("A.java","public class A {\n" +
                " //-@ model int i;\n" +
                " }"
                );
    }


}
