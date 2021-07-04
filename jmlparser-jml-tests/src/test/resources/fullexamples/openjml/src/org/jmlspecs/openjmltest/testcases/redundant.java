package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

/** This tests that for_example and implies_that sections parse properly; 
 * checks the proper use of keywords in them; checks restrictions on
 * normal and exceptional spec cases
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class redundant extends TCBase {

    // FIXME - what about redundantly keywords

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** basic implies_that and for_example */
    @Test
    public void testRedundant() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that  ensures false; for_example ensures true; */\n void m(){} }");
    }

    /** implies_that and for_example with behavior, example */
    @Test
    public void testRedundant1() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that behavior ensures false; for_example example ensures true; */\n void m(){} }");
    }

    /** implies_that and for_example with normal_behavior, normal_example */
    @Test
    public void testRedundant1a() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that normal_behavior ensures false; for_example normal_example ensures true; */\n void m(){} }");
    }

    /** implies_that and for_example with exceptional_behavior, exceptional_example */
    @Test
    public void testRedundant1b() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that exceptional_behavior signals_only Exception; for_example exceptional_example requires true; */\n void m(){} }");
    }

    /** mixed up behavior and example */
    @Test
    public void testRedundant2() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ ensures true; implies_that example ensures false; for_example behavior ensures true; */\n void m(){} }"
                ,"/A.java:1: warning: A example specification case must appear in a for_example section",49
                ,"/A.java:1: warning: A behavior specification case must not appear in a for_example section",84
            );
    }

    /** mixed up normal_behavior and normal_example */
    @Test
    public void testRedundant2a() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ ensures true; implies_that normal_example ensures false; for_example normal_behavior ensures true; */\n void m(){} }"
                ,"/A.java:1: warning: A normal_example specification case must appear in a for_example section",49
                ,"/A.java:1: warning: A normal_behavior specification case must not appear in a for_example section",91
            );
    }

    /** mixed up exceptional_behavior and exceptional_example */
    @Test
    public void testRedundant2b() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ ensures true; implies_that exceptional_example requires false; for_example exceptional_behavior requires true; */\n void m(){} }"
                ,"/A.java:1: warning: A exceptional_example specification case must appear in a for_example section",49
                ,"/A.java:1: warning: A exceptional_behavior specification case must not appear in a for_example section",97
            );
    }

    /** also connectors */
    @Test
    public void testRedundant3() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that  ensures false; also requires true; for_example ensures true; also normal_example ensures false; */\n void m(){} }");
    }

    /** visibility */
    @Test
    public void testRedundant4() {
        helpTCF("A.java","public class A { /*@ ensures true; implies_that public behavior ensures false; */\n void m(){} }");
    }
    
    /** visibility */
    @Test
    public void testRedundant4b() {
        helpTCF("A.java","public class A { /*@ ensures true; for_example public normal_example ensures false; */\n void m(){} }");
    }

}
