package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Ignore;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnew extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B";
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        main.addOptions("-code-math=java","-spec-math=java");  // FIXME - errors if we use bigint math
        //main.addOptions("-verboseness=4");
        expectedNotes = 0;
        main.addOptions("-jmltesting");
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJava() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { System.out.println(\"HELLO WORLD\"); }}"
                ,"HELLO WORLD"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaExit() {
        expectedRACExit = 5;
        helpTCX("tt.TestJavaExit","package tt; public class TestJavaExit { public static void main(String[] args) { System.exit(5); }}"
                );
    }

    /** Basic Hello World test, with no RAC tests triggered */
    @Test public void testJavaNull() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  }}"
                );
    }

    /** Simple test of output from a JML set statement */
    @Test public void testJML() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ ghost int i = 0; \n //@ set i = 1; \n //@ set System.out.println(i); \n System.out.println(\"END\"); }}"
                ,"1"
                ,"END"
                );
    }

    /** JML assert statement failure */
    @Test public void testAssertion() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestAssert.java:2: JML assertion is false"
                ,"END"
                );
    }

    /** JML labeled assert statement failure */
    @Test public void testAssertion2() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { \n//@ assert false: \"ABC\"; \n System.out.println(\"END\"); }}"
                ,"ABC"
                ,"END"
                );
    }

    /** Tests that an optional argument on a JML assert is converted to a String and is what is printed as an error message */
    @Test public void testAssertion3() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert false: (int)args.length; \n System.out.println(\"END\"); }}"
                ,"0"
                ,"END"
                );
    }

    /** Tests that an optional argument on a JML assert is converted to a String and is what is printed as an error message */
    @Test public void testAssertion3a() {
        helpTCX("tt.TestAssert","package tt; public class TestAssert { public static void main(String[] args) { //@ assert true: args.length; \n System.out.println(\"END\"); }}"
                ,"END"
                );
    }

    /** Assumption failure */
    @Test public void testAssumption() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML assumption is false"
                ,"END"
                );
    }

    /** Labeled assumption failure */
    @Test public void testAssumption2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ assume false: \"DEF\"; \n System.out.println(\"END\"); }}"
                ,"DEF"
                ,"END"
                );
    }

    /** Failed unreachable statement */
    @Test public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { //@ unreachable; \n System.out.println(\"END\"); }}"
                ,"/tt/TestJava.java:1: JML unreachable statement reached"
                ,"END"
                );
    }

    /** Successful precondition */
    @Test public void testPrecondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i == 0; */ static void m(int i) {} " +
                "}"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(0); System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ \n" +
                " static public void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    /** Failed precondition */
    @Test public void testPrecondition3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); \n" +
                " m(-1); \n" +
                " m(0); \n" +
                " System.out.println(\"END\"); }\n" +
                " /*@ requires i > 0; */ \n" +
                " /*@ requires i < 0; */ \n" +
                " static public void m(int i) {} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"/tt/TestJava.java:4: JML precondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:6: JML precondition is false"
                ,"END"
                );
    }
    
    /** Failed precondition with nowarn */
    @Test public void testPrecondition2NoWarn() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); //@ nowarn Precondition;\n" +
                "System.out.println(\"END\"); }\n" +
                " /*@ requires i != 0; */ //@ nowarn Precondition;\n" +
                " static void m(int i) {} \n" +
                "}"
                ,"END"
                );
    }
    
    @Test public void testNonnullPrecondition() {
        main.addOptions("-racShowSource=true");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n" + 
                "public static void main(String[] args) { \n" +
                " m(null,1); \n" +
                " System.out.println(\"END\"); }\n" +
                " /*@ requires true; */ \n" +
                " static public void m(/*@non_null*/ Object o, int i) {\n" +
                " }\n" +
                "}"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ," m(null,1); "
                ,"  ^"
                ,"/tt/TestJava.java:6: Associated declaration"
                ," static public void m(/*@non_null*/ Object o, int i) {"
                ,"                    ^"
                ,"/tt/TestJava.java:5: JML precondition is false"
                ," /*@ requires true; */ "
                ,"     ^"
                ,"END"
                );
    }
    
    @Test public void testNonnullPrecondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(null,1); System.out.println(\"END\"); }\n" +
                " static public void m(/*@non_null*/ Object o, int i) {} " +
                "}"
                ,"/tt/TestJava.java:1: JML precondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testNonnullPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null,1); \n" +
                "System.out.println(\"END\"); }\n" +
                " static public /*@non_null*/Object m( /*@nullable*/Object o, int i)\n" +
                "{ return null; } " +
                "}"
                ,"/tt/TestJava.java:4: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
    }
    
    // TODO need multiple requires, multiple spec cases

    @Test public void testPostcondition() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures k == i; */ static int m(int i) { k = i; return 13; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static public int k = 0; \n" +
                " /*@ ensures k == 0; */ \n" +
                " static public int m(int i) { k = i; return 13; } " +
                "}"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
    }

    @Test public void testPostcondition1Nowarn() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } /*@ nowarn Postcondition;*/\n" +
                " static int k = 0; \n" +
                " /*@ ensures k == 0; */ \n"+
                " static int m(int i) { k = i; return 13; }/*@ nowarn Postcondition;*/ " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ requires true; \nensures true; \nalso \nrequires false; \nensures k == 0; */ static void m(int i) { k = i; } " +
                "}"
                ,"END"
                );
    }

    @Test public void testPostcondition4() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(1); System.out.println(\"END\"); } \n" +
                " static public int k = 0; \n" +
                " /*@ requires true; \n" +
                "     ensures k != i; \n" +
                "     also \n" +
                "     requires true; \n" +
                "     ensures k == 0; */ \n" +
                " static public void m(int i) { k = i; } " +
                "}"
                ,"/tt/TestJava.java:9: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:9: JML postcondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:8: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testPostcondition5() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String[] args) { \n"
                +"    org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"    m(1); \n"
                +"    System.out.println(\"END\"); \n"
                +"  } \n"
                +"  static int k = 0; \n"
                +"  /*@   requires true; \n"
                +"        ensures k != i; \n" 
                +"      also \n"
                +"        requires true; \n"
                +"        ensures k == 0; */\n"
                +"  static void m(int i) { k = i; } " +
                "}"
                ,"Exception in thread \"main\" org.jmlspecs.utils.JmlAssertionError: /tt/TestJava.java:14: JML postcondition is false"
                ,"/tt/TestJava.java:10: Associated declaration"
                ,"\tat org.jmlspecs.utils.Utils.createException(Utils.java:103)"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:55)"
                ,"\tat tt.TestJava.m(TestJava.java:1)" // FIXME - should be line 14
                ,"\tat tt.TestJava.main(TestJava.java:5)"
                );
    }
    
    @Test public void testSignals() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n"
                +"     signals (java.io.FileNotFoundException e) e == null; */\n"
                +"static public void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignals2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static public int k = 0; \n"
                +" /*@ requires true; \nsignals (java.io.FileNotFoundException e) e == null; */\n"
                +"static public void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML signals condition is false"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testSignalsOnly() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only \\nothing; */\n"
                +"static public void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause: java.io.FileNotFoundException" // check by callee
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause: java.io.FileNotFoundException" // check of postcondition assumption by caller
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnly1() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"END"
                );
    }

    @Test public void testSignalsOnly2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \nsignals_only java.io.FileNotFoundException; */\n"
                +"static void m(int i) throws Exception, java.io.FileNotFoundException { throw new Exception(); } "
                +"}"
                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause: java.lang.Exception"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause: java.lang.Exception"
                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new RuntimeException(); } "
                +"}"
//                ,"/tt/TestJava.java:8: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:8: Associated declaration"
//                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:8: Associated declaration"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault1() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" /*@ requires true; \n*/\n"
                +"static void m(int i) throws java.io.FileNotFoundException { throw new java.io.FileNotFoundException(); } "
                +"}"
                ,"END"
                );
    }

    @Test public void testSignalsOnlyDefault2() {
        helpTCX("tt.TestJava","package tt; public class TestJava {\n"
                +" public static void main(String[] args) throws RuntimeException { \n"
                +"   try { m(1); } catch (Exception e) {} System.out.println(\"END\"); \n"
                +"} \n"
                +"static int k = 0; \n"
                +" \n"
                +"static void m(int i) \n"
                +"    throws java.io.FileNotFoundException \n"
                +"   { throw new RuntimeException(); }\n"
                +"}"
//                ,"/tt/TestJava.java:7: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:7: Associated declaration"
//                ,"/tt/TestJava.java:3: JML unexpected exception for the signals_only clause"
//                ,"/tt/TestJava.java:7: Associated declaration"
                ,"END"
                );
    }

    @Test public void testResult() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) {  m(1); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures \\result == 4; */ static int m(int i) { return 4; } " +
                "}"
                ,"END"
        );
    }

    @Test public void testResult1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +" m(1); \n"
                +" System.out.println(\"END\"); } \n"
                +" static int k = 0; \n" 
                +" /*@ ensures \\result == 4; */ \n"
                +" static public int m(int i) { \n"
                +" return 5; } "
                +"}"
                ,"/tt/TestJava.java:6: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"END"
        );
    }
    
    @Test public void testLabel() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\result == 1); */ static public int m(int i) { return i; } " +
                "}"
                ,"LABEL ENS = true"
                ,"LABEL ENS = true"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testLabel2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " /*@ ensures (\\lbl ENS (\\lbl RES \\result) == 1); */ static public int m(int i) { return i; } " +
                "}"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"LABEL RES = 1"
                ,"LABEL ENS = true"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL RES = 0"
                ,"LABEL ENS = false"
                ,"/tt/TestJava.java:1: JML postcondition is false"
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testOld() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static public int k = 0; \n" +
                " /*@ ensures (\\lbl ENS \\old(k)) == k; */ static public int m(int i) { k=i; return i; } " +
                "}"
                ,"LABEL ENS = 0" // k==0 at beginning of m(1)
                ,"/tt/TestJava.java:2: JML postcondition is false" // postcondition false because k is now 1
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 0"
                ,"/tt/TestJava.java:1: JML postcondition is false" // caller check, after m(1)
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 1" // k==1 at beginning of m(0)
                ,"/tt/TestJava.java:2: JML postcondition is false" // callee check
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"LABEL ENS = 1"
                ,"/tt/TestJava.java:1: JML postcondition is false" // caller check, after m(0)
                ,"/tt/TestJava.java:2: Associated declaration"
                ,"END"
        );        
    }
    
    @Test public void testOld2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { //@ assert (\\lbl AST \\old(k)) == 0; \n k=i; //@ assert (\\lbl AST2 \\old(k)) == 0;\n //@ assert (\\lbl AST3 k) == 0; \n return i; } " +
                "}"
                ,"LABEL AST = 0"
                ,"LABEL AST2 = 0"
                ,"LABEL AST3 = 1"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"LABEL AST = 1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"LABEL AST2 = 1"
                ,"/tt/TestJava.java:3: JML assertion is false"
                ,"LABEL AST3 = 0"
                ,"END"
        );        
    }
    
    @Test public void testOld3() {  // FIXME - \old at a label not working for RAC
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
                + "public static void main(String[] args) { \n"
                + "  m(1); m(0); \n"
                + "  System.out.println(\"END\"); "
                + "} \n"
                + "static int k = 0; \n"
                + "static int m(int i) { \n"
                + "  //@ ghost int p = (\\lbl AST \\old(k)); \n"
                + "  k=i; \n"
                + "  lab: k = 9+i; \n"
                + "  //@ ghost int kk =  (\\lbl AST2 \\old(k));\n "
                + "  //@ set kk = (\\lbl AST3 k); \n "
                + "  //@ set kk = (\\lbl AST4 \\old(k,lab)); \n "
                + "  return i; } "
                + "}"
                ,"LABEL AST = 0"  // k==0 at beginning of m(1)
                ,"LABEL AST2 = 0" // k==0 at beginning of m(1)
                ,"LABEL AST3 = 10" // k currently 10 in m(1)
                ,"LABEL AST4 = 1" // k was 1 at lab
                                  // k is 10 at exit of m(1)
                ,"LABEL AST = 10"  // so k is 10 at beginning of m(0) 
                ,"LABEL AST2 = 10" //  k is 10 at beginning of m(0)
                ,"LABEL AST3 = 9"  // k is 9 just after lab
                ,"LABEL AST4 = 0" // k was 0 (== i) at lab
                ,"END"
        );        
    }
    
    @Test public void testInformal() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { m(1); m(0); System.out.println(\"END\"); } static int k = 0; \n" +
                " static int m(int i) { System.out.println(i); //@ assert (i==0) <==> (* informal *); \n return i; } " +
                "}"
                ,"1"
                ,"/tt/TestJava.java:2: JML assertion is false"
                ,"0"
                ,"END"
                );
    }

    @Test public void testElemtype() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" 
                +"Object o = new String[3]; Object oo = new int[5]; Object o3 = new Integer(4);\n"
                +"//@ ghost nullable java.lang.Class t; ghost nullable \\TYPE tt; \n"
                +"//@ set tt = (\\lbl A \\elemtype(\\typeof(o)));\n"
                +"//@ set tt = (\\lbl B \\elemtype(\\typeof(oo)));\n"
                +"//@ set tt = (\\lbl C \\elemtype(\\typeof(o3)));\n"
                +"//@ set t = (\\lbl D \\elemtype(java.lang.Class.class));\n"
                +"//@ set t = (\\lbl E \\elemtype(java.lang.Boolean[].class));\n"
                +"System.out.println(\"END\"); } \n"
                +"}"
                ,"LABEL A = class java.lang.String"
                ,"LABEL B = int"
                ,"LABEL C = null"
                ,"LABEL D = null"
                ,"LABEL E = class java.lang.Boolean"
                ,"END"
                );
        
    }
    

    @Test public void testTypeOfA() {
        helpTCX("tt.TestJava","package tt; import static org.jmlspecs.lang.JML.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object()); m(new String()); m(Boolean.TRUE); System.out.println(\"END\"); } \n" +
                " //@ requires JML.informal(\"asd\") && (\\lbl CLS \\erasure(\\typeof(i))) == Object.class; \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.lang.Object"
                ,"LABEL CLS = class java.lang.Object"
                ,"CLASS class java.lang.Object"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.lang.String"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.String"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.lang.Boolean"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.lang.Boolean"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf1() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(new Object[1]); m(new String[2]); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class [Ljava.lang.Object;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.Object;"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class [Ljava.lang.String;"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class [Ljava.lang.String;"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == \\type(Object); \n" +
                " static public void m(int i) { \n" +
                "//@ assert (\\lbl AST \\typeof(true)) == \\typeof(true); \n" +
                "//@ assert (\\lbl AST2 \\typeof((short)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST3 \\typeof((long)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST4 \\typeof((byte)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST5 \\typeof('c')) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST6 \\typeof(\"c\")) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST7 \\typeof((float)0)) != \\typeof(true); \n" +
                "//@ assert (\\lbl AST8 \\typeof((double)0)) != \\typeof(true); \n" +
                "} " +
                "}"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = int"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"LABEL AST = boolean"
                ,"LABEL AST2 = short"
                ,"LABEL AST3 = long"
                ,"LABEL AST4 = byte"
                ,"LABEL AST5 = char"
                ,"LABEL AST6 = class java.lang.String"
                ,"LABEL AST7 = float"
                ,"LABEL AST8 = double"
                ,"END"
                );
        
    }
    
    @Test public void testTypeOf3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "//@ assert (\\lbl AST9 \\typeof(5/0)) == \\typeof(5/0); \n" +
                "//@ assert (\\lbl AST10 \\typeof(5.0/0.0)) != \\typeof(5/0); \n" +
                "} " +
                "}"
                ,"LABEL AST9 = int"
                ,"LABEL AST10 = double"
                ,"END"
                );
        
    }

    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf4() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>()); m(new LinkedList<Integer>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == ( \\type(LinkedList<Integer>) ); \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:2: JML precondition is false"
//                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    
    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf5() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>()); m(new LinkedList<Integer>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) == ( \\type(LinkedList<Integer>) ); \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:2: JML precondition is false"
//                ,"/tt/TestJava.java:3: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
//                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.util.HashSet"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    
    // FIXME - want typeof to return a JML type with type parameter information
    @Test public void testTypeOf6() {
        helpTCX("tt.TestJava","package tt; import java.util.*; public class TestJava { public static void main(String[] args) { \n" +
                "m(new LinkedList<String>());  m(new HashSet<Integer>()); System.out.println(\"END\"); } \n" +
                " //@ requires (\\lbl CLS \\typeof(i)) != ( \\type(LinkedList<Integer>) ); \n" +
                " static public void m(/*@nullable*/Object i) { System.out.println(\"CLASS \" + i.getClass()); } " +
                "}"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"LABEL CLS = class java.util.LinkedList"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"CLASS class java.util.LinkedList"
                ,"LABEL CLS = class java.util.HashSet"
                ,"LABEL CLS = class java.util.HashSet"
                ,"CLASS class java.util.HashSet"
                ,"END"
                );
        
    }
    

    @Test public void testNonnullelement() {
        expectedRACExit = 1;
        helpTCX("tt.TestJava","package tt; public class TestJava { static int z = 0; public static void main(String[] args) { \n" +
                "String[] s2null = new String[]{null,\"B\"}; \n" +
                "String[] s2 = new String[]{\"A\",\"B\"}; \n" +
                "m(new Object[]{}); \n" +
                "m(new String[]{\"A\"}); \n" +
                "m(s2); \n" +
                "m(s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2null); \n" +
                "//@ assert \\nonnullelements(s2,s2); \n" +
                        // Tests shortcut evaluation - should evaluate all arguments first
                "//@ assert \\nonnullelements(s2null,new Integer[]{5/z}); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(Object[] o) { \n" +
                "//@ assert (\\lbl ELEM \\nonnullelements(o)); \n" +
                "} " +
                "}"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = true"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:13: JML assertion is false"
                ,"/tt/TestJava.java:8: JML assertion is false"
                ,"/tt/TestJava.java:10: JML Division by zero"
                ,"Exception in thread \"main\" java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:10)"
                );
        
    }
    
    @Test public void testNonnullelement2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m(/*@nullable*/Object[] o) { \n" +
                "//@ assert (\\lbl ELEM \\nonnullelements((\\lbl O o))); \n" +
                "} " +
                "}"
                ,"LABEL O = null"
                ,"LABEL ELEM = false"
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
                );
        
    }
    
    @Test public void testLbl() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } \n" +
                "static int i = 0; static String n = \"asd\";\n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl STRING \"def\") != null; \n" +
                "++i; //@ assert (\\lbl SHORT (short)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl LONG (long)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl BYTE (byte)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl INT (int)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl FLOAT (float)(i)) != 0; \n" +
                "++i; //@ assert (\\lbl DOUBLE (double)(i)) != 0; \n" +
                "//@ assert (\\lbl CHAR n.charAt(0)) != 0; \n" +
                "//@ assert (\\lbl BOOLEAN (i == 0)) ; \n" +
                "//@ assert (\\lbl OBJECT o) == null; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "} " +
                "}"
                ,"LABEL STRING = def"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL INT = 4"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = a"
                ,"LABEL BOOLEAN = false"
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"LABEL OBJECT = null"
                ,"LABEL STRING = abc"
                ,"END"
                );
        
    }
    
    @Test public void testLblConst() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(null); \n" +
                "System.out.println(\"END\"); } static int i = 0; \n" +
                " static void m(/*@nullable*/ Object o) { \n" +
                "//@ assert (\\lbl OBJECT null) == null; \n" +
                "//@ assert (\\lbl INT (int)(4)) != 0; \n" +
                "//@ assert (\\lbl SHORT (short)(1)) != 0; \n" +
                "//@ assert (\\lbl LONG (long)(2)) != 0; \n" +
                "//@ assert (\\lbl BYTE (byte)(3)) != 0; \n" +
                "//@ assert (\\lbl FLOAT (float)(5)) != 0; \n" +
                "//@ assert (\\lbl DOUBLE (double)(6)) != 0; \n" +
                "//@ assert (\\lbl CHAR 'a') != 0; \n" +
                "//@ assert (\\lbl BOOLEAN true) ; \n" +
                "//@ assert (\\lbl STRING \"abc\") != null; \n" +
                "} " +
                "}"
                ,"LABEL OBJECT = null"
                ,"LABEL INT = 4"
                ,"LABEL SHORT = 1"
                ,"LABEL LONG = 2"
                ,"LABEL BYTE = 3"
                ,"LABEL FLOAT = 5.0"
                ,"LABEL DOUBLE = 6.0"
                ,"LABEL CHAR = a"
                ,"LABEL BOOLEAN = true"
                ,"LABEL STRING = abc"
                ,"END"
                );
        
    }
    
    @Test public void testLblX() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); ma(); mg(); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(int); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(boolean); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Object); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(Object); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "}\n" +
                " static void ma() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.String[]); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(String[]); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String[][]); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String[][]); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "} \n" +
                " static void mg() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Class<Integer>); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ ghost boolean bbb = (\\lbl TRUE Class.class == \\erasure(\\type(Class))); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = class java.lang.Object"
                ,"LABEL TYP2 = class java.lang.Object"
                ,"LABEL TYP3 = class java.lang.String"
                ,"LABEL TYP4 = class java.lang.String"
                ,"LABEL TYP1 = class [Ljava.lang.String;"
                ,"LABEL TYP2 = class [Ljava.lang.String;"
                ,"LABEL TYP3 = class [[Ljava.lang.String;"
                ,"LABEL TYP4 = class [[Ljava.lang.String;"
                ,"LABEL TYP1 = class java.lang.Class<class java.lang.Integer>"
                ,"LABEL TRUE = true"
                ,"LABEL TYP2 = class java.lang.Class<class java.lang.Integer>"
                ,"END"
                );
        
    }
    
    @Test
    public void testTypelc() { 
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); ma(); mg(); \n" +
                "System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(int); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(boolean); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Object); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(Object); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "}\n" +
                " static void ma() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.String[]); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\type(String[]); \n" +
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(java.lang.String[][]); \n" +
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(String[][]); \n" +
                "//@ set c = (\\lbl TYP4 c); \n" +
                "} \n" +
                " static void mg() { \n" +
                "//@ ghost \\TYPE c; \n" +
                "//@ set c = \\type(java.lang.Class<Integer>); \n" +
                "//@ set c = (\\lbl TYP1 c); \n" +
                "} " +
                "}"
                ,"LABEL TYP1 = int"
                ,"LABEL TYP2 = boolean"
                ,"LABEL TYP1 = class java.lang.Object"
                ,"LABEL TYP2 = class java.lang.Object"
                ,"LABEL TYP3 = class java.lang.String"
                ,"LABEL TYP4 = class java.lang.String"
                ,"LABEL TYP1 = class [Ljava.lang.String;"
                ,"LABEL TYP2 = class [Ljava.lang.String;"
                ,"LABEL TYP3 = class [[Ljava.lang.String;"
                ,"LABEL TYP4 = class [[Ljava.lang.String;"
                ,"LABEL TYP1 = class java.lang.Class<class java.lang.Integer>"
                ,"END"
                );
        
    }

    @Test
    public void testSubtype() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(); mm(); \n" +
                "System.out.println(\"END\"); } \n" +
                "static Object o = new Object(); \n" +
                "static Object oo = new String(); \n" +
                "static Object ob = Boolean.FALSE; \n" +
                "static String s = new String(); \n" +
                "static Boolean b = Boolean.TRUE; \n" +
                " static void m() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = o.getClass() <: o.getClass(); \n" + // Object <: Object  // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(o); \n" +  // Object <: Object // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\typeof(o) <: \\typeof(oo); \n" + // Object <: String // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\typeof(oo) <: \\typeof(o); \n" + // String <: Object // \TYPE
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\typeof(ob) <: \\typeof(oo); \n" + // Boolean <: String // \TYPE
                "//@ set c = (\\lbl TYP5 c); \n" +
                "}\n" +
                " static void mm() { \n" +
                "//@ ghost boolean c; \n" +
                "//@ set c = s.getClass() <: b.getClass(); \n" + // String <: Boolean // Class
                "//@ set c = (\\lbl TYP1 c); \n" +
                "//@ set c = \\typeof(s) <: \\typeof(b); \n" +  // String <: Boolean // \TYPE
                "//@ set c = (\\lbl TYP2 c); \n" +
                "//@ set c = \\type(int) <: \\typeof(o); \n" + // int <: Object // \TYPE
                "//@ set c = (\\lbl TYP3 c); \n" +
                "//@ set c = \\type(int) <: \\type(int); \n" + // int <: int  // false
                "//@ set c = (\\lbl TYP4 c); \n" +
                "//@ set c = \\type(int) <: \\type(boolean); \n" + // int <: boolean
                "//@ set c = (\\lbl TYP5 c); \n" +
                "}\n" +
                "}"
                ,"LABEL TYP1 = true"
                ,"LABEL TYP2 = true"
                ,"LABEL TYP3 = false"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP5 = false"
                ,"LABEL TYP1 = false"
                ,"LABEL TYP2 = false"
                ,"LABEL TYP3 = false"
                ,"LABEL TYP4 = true"
                ,"LABEL TYP5 = false"
                ,"END"
                );
        
    }

    @Test public void testUndefined() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); m(2); System.out.println(\"END\"); } \n" +
                " //@ requires 10/i != 0; \n" +
                " //@ ensures 10/(i-1) == 0; \n" +
                " static public void m(int i) { \n" +
                "   System.out.println(\"VALUE \" + i); \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"JML undefined precondition - exception thrown" // FIXME - this should have a line number
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:3: JML Division by zero"
                ,"Runtime exception while evaluating preconditions - preconditions are undefined in JML"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.m(TestJava.java:3)"
                ,"\tat tt.TestJava.main(TestJava.java:2)"
                ,"VALUE 0"
                ,"VALUE 1"
                ,"/tt/TestJava.java:4: JML Division by zero"
                ,"Runtime exception while evaluating postconditions - postconditions are undefined in JML"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.m(TestJava.java:4)"
                ,"\tat tt.TestJava.main(TestJava.java:2)"
                ,"/tt/TestJava.java:4: JML Division by zero"
                ,"JML undefined postcondition - exception thrown"
                ,"java.lang.ArithmeticException: / by zero"
                ,"\tat tt.TestJava.main(TestJava.java:4)"
                ,"VALUE 2"
                ,"/tt/TestJava.java:5: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:2: JML postcondition is false"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"END"
                );
        // FIXME - would like to make the stack traces above more helpful
    }
    
    // tests that requires clauses in the same spec case are evaluated in order as if connected by &&
    // (if not, in this case we would get an exception)
    @Test public void testUndefined2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(0); m(1); System.out.println(\"END\"); } \n" +
                " //@ requires i != 0; \n" +
                " //@ requires 10/i == 10; \n" +
                " static public void m(int i) { \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:2: JML precondition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:3: JML precondition is false"
                ,"END"
                );
        
    }
    
    @Test public void testSpecFile() {
        addMockFile("$A/tt/A.jml","package tt; public class A { //@ ghost public static int i = 0;\n  //@ public invariant i == 0; \n //@ requires i == 1;\n static public int m(); }");
        helpTCX("tt.A","package tt; public class A { static public int m() { return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/tt/A.java:2: JML precondition is false"
                ,"/tt/A.java:1: Associated declaration"
                ,"/$A/tt/A.jml:3: JML precondition is false"
                ,"END"
                );
        
    }

    @Test public void testSpecFile2() {
        addMockFile("$A/tt/A.jml","package tt; public class A { //@ ghost static int i = 0;\n  //@ invariant i == 0; \n //@ ensures i == 1;\n static int m(); }");
        helpTCX("tt.A","package tt; public class A { static int m() { //@ set i = 1; \n return 0; }  \n public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"END"
                );
        
    }

    @Test public void testSpecModelMethod() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model static pure public int mm() { return 5; } */ \n"
                +"//@ ghost static public int i = 0;\n  "
                +"//@ public invariant i == 0; \n //@ ensures i == 1;\n static public int m(); "
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { static public int m() { \n"
                +"  //@ set i = mm(); \n"
                +"  return 0; }  \n"
                +" public static void main(String[] args) { m(); System.out.println(\"END\"); }}"
                ,"/tt/A.java:1: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"/tt/A.java:4: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"END"
                );
        
    }

    @Test
    public void testSpecModelClass() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"/*@ model public static class AA { static public int mm() { return 5; }} */ \n"
                +"//@ ghost public static int i = 0;\n  "
                +"//@ public invariant i == 0; \n "
                +"//@ ensures i == 0;\n "
                +"static public int m() { \n"
                +"  //@ set i = AA.mm(); \n"
                +"  return 0; \n"
                +"}  \n "
                +"public static void main(String[] args) { \n"
                +"  m(); \n"
                +"  System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:6: JML postcondition is false"  // TODO: Would like this to be line 8
                ,"/tt/A.java:5: Associated declaration"
                ,"/tt/A.java:11: JML postcondition is false"
                ,"/tt/A.java:5: Associated declaration"
                ,"END"
                );
        
    }
    
    @Test
    public void testSpecModelClass2() { 
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"/*@ model public static class AB { static public int mm() { return 5; }} */ \n"
                +"//@ ghost public static int i = 0;\n  "
                +"//@ public invariant i == 0; \n "
                +"//@ ensures i == 0;\n "
                +"static public int m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static public int m() { \n"
                +"  //@ set i = AB.mm(); \n"
                +"  return 0; \n"
                +"}  \n "
                +"public static void main(String[] args) { \n"
                +"  m(); \n"
                +"  System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:2: JML postcondition is false"  // TODO: Would like this to be line 4
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"/tt/A.java:7: JML postcondition is false"
                ,"/$A/tt/A.jml:5: Associated declaration"
                ,"END"
                );
        
    }
    
    @Test public void testStaticInvariant() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static public invariant i == 0; \n "
                +"public static void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static public int i = 0;  \n "
                +"static public void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()" // callee invariant by callee
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // callee invariant by caller
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // caller on reentering after calling m
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:6: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // caller on leaving to call m
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // callee invariant by caller
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()" // callee invariant by callee
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                );
    }

    @Test public void testStaticInvariant2() { 
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ static public invariant i == 0; \n "
                +"public void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"static public int i = 0;  \n "
                +"public void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); i = 5; \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"  // Leaving m
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:5: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Reentering main from m
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:6: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on entering method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                // FIXME - why are these and the lines below suddenly no longer output
//                ,"/tt/A.java:7: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
//                ,"/$A/tt/A.jml:2: Associated declaration"

                ,"/tt/A.java:7: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:7: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:8: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on entering method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
//                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.A())"
//                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                ,"/tt/A.java:10: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:2: Associated declaration"
                );
    }

    @Test public void testInvariant() { 
        main.addOptions("-racShowSource=true");
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ public invariant i == 0;\n"
                +"public void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"public int i = 0; static int j; \n"
                +"public void m() { i = 1-i; }  \n"
                +"public static void main(String[] args) { \n"
                +"new A().m();\n"
                +"j = 0; System.out.println(\"MID\"); j = 1;\n"
                +"new A().m();\n"
                +"j = 2; System.out.println(\"END\");\n"
                +"}}"
                
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()" // Leaving m(), Line 5
                ,"public void m() { i = 1-i; }  "
                ,"            ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"/tt/A.java:5: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"new A().m();"
                ,"         ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"MID"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"public void m() { i = 1-i; }  "
                ,"            ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"/tt/A.java:7: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"new A().m();"
                ,"         ^"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"//@ public invariant i == 0;"
                ,"           ^"
                ,"END"
                );
    }

    @Test public void testInitially() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ public initially i == 1; \n "
                +"//@ public initially j == 1; \n "
                +"//@ public invariant i == j; \n "
                +" public void m(); \n"
                +"/*@ assignable j; */\n "
                +"public A();  \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"public int i = 0;  \n"
                +"static public int j = 0;  \n"
                +"public A() { i++; j++; }  \n"
                +"public void m() { i++; j++; }  \n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"START\"); \n"
                +"new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"new A().m(); \n"
                +"System.out.println(\"END\");\n "
                +"}}"
                ,"START"
                ,"MID"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:4: JML initially clause is false at exit from constructor"
                ,"/$A/tt/A.jml:3: Associated declaration"
                ,"/tt/A.java:10: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:10: JML initially clause is false at exit from constructor"
                ,"/$A/tt/A.jml:3: Associated declaration"
                ,"/tt/A.java:10: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:10: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:5: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:5: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"/tt/A.java:10: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/A.jml:4: Associated declaration"
                ,"END"
                );
    }


    @Test public void testConstraint() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ constraint i == \\old(i)+1; \n "
                +"void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 1;  \n "
                +"void m() { i *= 2; }  \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"System.out.println(\"START\"); \n"
                +"a.m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"a.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"START"
                ,"MID"
                ,"/tt/A.java:3: JML constraint clause is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"/tt/A.java:9: JML constraint clause is false on leaving method"
                ,"/$A/tt/A.jml:2: Associated declaration"
                ,"END"
                );
    }

    @Test public void testHelper() {
        addMockFile("$A/tt/A.jml","package tt; public class A { \n" 
                +"//@ invariant i == 0; \n "
                +"/*@ private helper */ void m(); \n"
                +"}"
                );
        helpTCX("tt.A","package tt; public class A { \n"
                +"int i = 0;  \n "
                +"private void m() { i = 1-i; }  \n "
                +"public static void main(String[] args) { \n"
                +"new A().m(); "
                +"System.out.println(\"MID\"); "
                +"new A().m(); "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"MID"
                ,"END"
                );
    }

    @Test public void testSuchThat() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n"
                +"//@ static model int i; \n"
                +"//@ static represents i \\such_that i == j+1; \n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"}"
                ,"/tt/A.java:4: Note: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",12
                ,"/tt/A.java:3: warning: JML model field is not implemented: i",22
                ,"END"
                );

    }
    
    @Test public void testModelField() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"//@ static ghost int ii; \n "
                +"}"
                ,"A 6"
                ,"A 11"
                ,"END"
                );

    }
    
    // FIXME - this results of this test are different when run standalone
    @Test public void testModelFieldST() {
        main.addOptions("-keys=DEBUG");
        expectedNotes = 0;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i \\such_that i==j+1; \n "
                +"//@ static represents i =j+1; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}"
                +"//@ static ghost int ii; \n "
                +"}"
                ,"/tt/A.java:4: Note: Not implemented for runtime assertion checking: relational represents clauses (\\such_that)",13
                ,"A 6"
                ,"A 11"
                ,"END"
                );

    }
    
    /** Duplicate represents */
    @Test public void testModelField1() {
        main.addOptions("-keys=DEBUG");
        continueAnyway = true;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n "
                +"//@ static model int i; \n "
                +"//@ static represents i = j+1; \n "
                +"//@ static represents i = j; \n "
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +" j = 10; \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:5: warning: Duplicate represents clause - only the first is used for RAC",13
                ,"A 6"
                ,"A 11"
                ,"END"
                );

    }
    
    // TODO - the following two tests fail when the compile policy is
    // SIMPLE instead of BY_TODO - for some reason the principal class
    // file (PA or QA) does not get written.
    
    /** Represents with super model field */
    @Test public void testModelField3() {
        continueAnyway = true; // That is, even though there are compile errors
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; \n "
                +"//@  represents i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\");\n"
                +"}}\n"
                +"class PB { //@ model  int i; \n}"
                ,"/tt/PA.java:13: warning: JML model field is not implemented: i",27
                ,"A 6"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }

    /** Represents with super model field */
    @Test public void testModelField3a() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA extends PB { \n"
                +" int j = 5; \n "
                +"//@  represents super.i = j+1; \n "
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new PA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class PB { //@ model protected int i; }\n"
                ,"/tt/PA.java:12: warning: JML model field is not implemented: i",39
                ,"A 6"
                ,"B 0"
                ,"B 6"
                ,"END"
                );

    }

    /** Using a model field in a field access */
    @Test public void testModelField1a() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.PA","package tt; public class PA { \n"
                +" static int j = 5; \n "
                +"//@  model int i; represents i = j; \n"
                +"public static void main(String[] args) { \n"
                +"PA a = new PA();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"PB b = new PB();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}} class PB { //@ model  int i; represents i = PA.j+1; \n\n}"
                ,"A 5"
                ,"B 6"
                ,"END"
                );

    }

    /** Represents with super model field */
    @Test public void testModelField4() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.QA","package tt; public class QA extends QB { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"QA a = new QA();\n"
                +"QB b = new QB();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new QA();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); \n"
                +"}} class QB { //@ model  int i; \n}"
                ,"/tt/QA.java:11: warning: JML model field is not implemented: i",30
                ,"A 0"
                ,"B 0"
                ,"B 0"
                ,"END"
                );

    }

    /** Model field with no represents */
    @Test public void testModelField2() {
        main.addOptions("-keys=DEBUG");
        expectedExit = 0;
        continueAnyway = true;
        helpTCX("tt.A","package tt; public class A { \n"
                +"static int j = 5; \n"
                +"//@ static model int i; \n"
                +"public static void main(String[] args) { \n"
                +"//@ debug System.out.println(\"A \" + i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: warning: JML model field is not implemented: i",22
                ,"A 0"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 2); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A false true"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier2() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<=i && i<=5; i >= 0); \n "
                +"//@ ghost boolean nn = (\\exists int i; 0<=i && i<=5; i >= 6); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
    
    /** Forall, exists quantifier */
    @Test public void testForallQuantifier3() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; ; i >= 0); \n "
                +"//@ ghost boolean nn = (\\exists int i; i == 4; i >= 6); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",25
                ,"/tt/A.java:4: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",26
                ,"A false false"
                ,"END"
        );
    }
    
    @Test public void testForallQuantifier4() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost boolean n = (\\forall int i; 0<i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ ghost boolean nn = (\\forall int i; 0<=i && i<=5; (\\exists int j; 0<=j && j < 5; j<i)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A true false"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i; 0 <= i && i <= 5; true); \n "
                +"//@ ghost long n2 = (\\num_of int i; 0 < i && i < 5; true); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 6 4"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifier3() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\num_of int i; 0 <= i && i < 5; i >= 2); \n "
                +"//@ ghost long nn = (\\num_of int i; 0 <= i && i < 5; false); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 0"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExt() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"public static void main(String[] argv) { \n "
                +"//  @ ghost int nnn = new org.jmlspecs.utils.Utils.ValueInt() { public int value(final Object[] args) { int count = 0; int lo = (Integer)(args[0]); int hi = (Integer)(args[1]); int i = lo; while (i <= hi) { if (i>=lo && i<=hi) count++; i++; } return count; }}.value(new Object[]{0,5});\n"
                +"//@ ghost int n = (\\num_of int i; 0 <= i && i < 5; i >= m); \n "
                +"//@ ghost int nn = (\\num_of int i; 0 <= i && i < 5; m > 0); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn ); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 3 5"
                ,"END"
        );
    }
    
    /** Numof quantifier */
    @Test public void testCountQuantifierExtE() {
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static int m = 2;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 3;\n"
                +"//@ ensures (\\num_of int i; 0 <= i && i < 5; i >= m) == 4;\n"
                +"public static void main(String[] argv) { \n "
                +"System.out.println(\"END\"); "
                +"}}"
                ,"END"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/tt/A.java:4: Associated declaration"
        );
    }
    
    // FIXME - quantifiers witrh multiple declarations
    /** Numof quantifier */
    @Test public void testCountTwo() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\num_of int i,j; 0 <= i && i <= 5 && 0 <= j && j < i; true); \n "
                +"//@ debug System.out.println(\"A \" + n1); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: Note: Runtime assertion checking is not implemented for this type or number of declarations in a quantified expression",23
                ,"A 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testSumQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\sum int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\sum int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 20 0"
                ,"END"
        );
    }
    
    /** Sum quantifier */
    @Test public void testProdQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\product int i; 0<i && i<=5; i+1); \n "
                +"//@ ghost int nn = (\\product int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 720 1"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; i+1); \n "
                +"//@ ghost int nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 -2147483648"
                ,"END"
        );
    }
    
    /** Max quantifier, with function call */
    @Test public void testMaxQuantifier2() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"  public static int inc(int i) { return i + 10; }\n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\max int i; 0<=i && i<=5 && (i%2)==0; inc(i)); \n "
                +"//@ ghost int nn = (\\max int i; -9<=i && i<=5 ; Math.abs(i)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 14 9"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ ghost short n2 = (\\min int i; 0<=i && i<=5; (short)(i+10)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over short */
    @Test public void testShortQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost short n1 = (\\max short i; 2<=i && i<=5; i); \n "
                +"//@ ghost short n2 = (\\min short i; 2<=i && i<=5; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ ghost byte n2 = (\\min int i; 2<=i && i<=5; (byte)i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over byte */
    @Test public void testByteQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost byte n1 = (\\max byte i; 2<=i && i<=5; i); \n "
                +"//@ ghost byte n2 = (\\min byte i; 2<=i && i<=5; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 2"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min int i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over long */
    @Test public void testLongQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n1 = (\\max long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ ghost long n2 = (\\min long i; 0<=i && i<=5; (i+10L)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15 10"
                ,"END"
        );
    }
    
    /**  quantifier over double */
    @Test public void testDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n1 = (\\max int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ ghost double n2 = (\\min int i; 0<=i && i<=5; (double)(i+10.5)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over float */
    @Test public void testFloatQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost float n1 = (\\max int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ ghost float n2 = (\\min int i; 0<=i && i<=5; (float)(i+10.5)); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 15.5 10.5"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ ghost char n2 = (\\min int i; 'a'<i && i<='q'; (char)i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /**  quantifier over char */
    @Test public void testCharQuantifierB() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost char n1 = (\\max char i; 'a'<i && i<='q'; i); \n "
                +"//@ ghost char n2 = (\\min char i; 'a'<i && i<='q'; i); \n "
                +"//@ debug System.out.println(\"A \" + n1 + \" \" + n2); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A q b"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost int n = (\\min int i; 0<=i && i<=5 && (i%2)==1; i+1); \n "
                +"//@ ghost int nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 2147483647"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (long)i+1); \n "
                +"//@ ghost long nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5 -2147483648"
                ,"END"
        );
    }
    
    /** Min quantifier */
    @Test public void testMinLongQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost long n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (long)i+1); \n "
                +"//@ ghost long nn = (\\min int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2 2147483647"
                ,"END"
        );
    }
    
    /** Max quantifier */
    @Test public void testMaxDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\max int i; 0<=i && i<=5 && (i%2)==0; (double)i+1); \n "
                +"//@ ghost double nn = (\\max int i; 0<i && i<0; i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 5.0 -2.147483648E9"
                ,"END"
        );
    }
    
    /** double quantifier */
    @Test public void testMinDoubleQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +"//@ ghost double n = (\\min int i; 0<=i && i<=5 && (i%2)==1; (double)i+1); \n "
                +"//@ ghost double nn = (\\min int i; 0<i && i<0; (double)i+1); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 2.0 1.7976931348623157E308"
                ,"END"
        );
    }
    
    /** boolean quantifier */
    @Test public void testBooleanQuantifier() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +" boolean bb = true;"
                +"//@ ghost int n = (\\sum boolean i; bb; (i?2:5)); \n "
                +"//@ ghost int nn = (\\sum boolean i; !i; (i?2:5)); \n "
                +"//@ ghost int nnn = (\\sum boolean i; i; (i?2:5)); \n "
                +"//@ ghost int nnnn = (\\sum boolean i; false; (i?2:5)); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn + \" \" + nnn + \" \" + nnnn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 7 5 2 0"
                ,"END"
        );
    }
    
    /** Object quantifier */
    @Test public void testObjectQuantifier() {
        expectedNotes = 0;
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.A","package tt; import java.util.*; public class A { \n"
                +"public static void main(String[] argv) { \n "
                +" List<Object> list = new LinkedList<Object>();\n"
                +"//@ ghost int n = (\\num_of Object o; list.contains(o); true); \n "
                +" Object oo = new Object(); list.add(new Object());\n"
                +"//@ ghost int nn = (\\num_of Object o; list.contains(o) && true; true); \n "
                +" list.add(oo);\n"
                +"//@ ghost int nnn = (\\num_of Object o; list.contains(o) && o == oo; true); \n "
                +"//@ debug System.out.println(\"A \" + n + \" \" + nn + \" \" + nnn); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"A 0 1 1"
                ,"END"
        );
    }
    
    /** Represents with super model field */
    @Test public void testModelField5a() {
        continueAnyway = true;
        addMockFile("$A/tt/B.java","package tt; class B{ //@ model int i; \n}");
        helpTCX("tt.A","package tt; public class A extends tt.B { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"tt.B b = new tt.B();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/B.java:1: warning: JML model field is not implemented: i",36
                ,"END"
                );

    }

    /** Represents with super model field */
    @Test public void testModelField5() {
        continueAnyway = true;
        main.addOptions("-keys=DEBUG");
        addMockFile("$A/tt/B.java","package tt; class B{ //@ model int i; \n}");
        helpTCX("tt.A","package tt; public class A extends tt.B { \n"
                +" int j = 5; \n "
                +"public static void main(String[] args) { \n"
                +"A a = new A();\n"
                +"tt.B b = new tt.B();\n"
                +"//@ debug System.out.println(\"A \" + a.i); \n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"b = new A();\n"
                +"//@ debug System.out.println(\"B \" + b.i); \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/$A/tt/B.java:1: warning: JML model field is not implemented: i",36
                ,"A 0"  //FIXME - check this
                ,"B 0"
                ,"B 0"
                ,"END"
                );

    }

    @Test public void testNullAssignment() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static String o=\"\",oo=\"\"; static Object ooo;\n"
                +"public static void main(String[] args) { \n"
                +"   oo = null;\n"
                +"   ooo = null;\n"
                +"   /*@ non_null*/ String local = \"\";\n"
                +"   local = (String)ooo;"
                +"System.out.println(\"END\"); "
                +"}} class B { //@ model  int i; represents i = 0; \n}"
                ,"/tt/A.java:4: JML assignment of null to a non_null variable"
                ,"/tt/A.java:7: JML assignment of null to a non_null variable"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null"
                );

    }

    @Test public void testNullAssignment2() {
        helpTCX("tt.A","package tt; import org.jmlspecs.annotation.*; @NullableByDefault public class A  { \n"
                +"/*@non_null*/ static Object o,oo; static Object ooo; \n"
                +"public static void main(String[] args) { \n"
                +"   A.oo = null;\n"
                +"   A.ooo = null;\n"
                +"System.out.println(\"END\"); "
                +"}} "
                ,"/tt/A.java:2: JML static initialization may not be correct: non-null static field has null value: o"
                ,"/tt/A.java:2: JML static initialization may not be correct: non-null static field has null value: oo"
                ,"/tt/A.java:4: JML assignment of null to a non_null variable"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null"
                ,"/tt/A.java:2: JML non-null field is null"
                );

    }

    @Test public void testNullReference() {
        expectedRACExit = 1;
        helpTCX("tt.A","package tt; import org.jmlspecs.annotation.*; public class A  { \n"
                +"/*@nullable*/static A a = null;\n"
                +"/*@nullable*/ A b = null;\n"
                +"static int i = 9;\n"
                +"public static void main(String[] args) { \n"
                +"   int j; j = A.i;\n"
                +"   j = a.i;\n" // No null dereference warning since i is static
                +"   try { j = a.b.i; } catch (NullPointerException e) {} \n"
                +"   //@ ghost int k; set k = A.i;\n"
                +"   //@ set k = a.i;\n"
                +"   //@ set k = a.b.i;\n"
                +"System.out.println(\"END\"); \n"
                +"}}"
                ,"/tt/A.java:8: JML A null object is dereferenced"
                ,"/tt/A.java:11: JML A null object is dereferenced within a JML expression"
                ,"Exception in thread \"main\" java.lang.NullPointerException"
                ,"\tat tt.A.main(A.java:11)"
                );

    }

    @Test public void testNullInitialization() {
        helpTCX("tt.A","package tt; /*@nullable_by_default*/ public class A  { \n"
                +"/*@non_null*/ static Object o,oo = null; \n"
                +"static String ooo = null;\n"
                +"//@ non_null ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ non_null*/ String local = ooo;\n"
                +"   //@ ghost non_null String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} "
                ,"/tt/A.java:2: JML null initialization of non_null field oo"
                ,"/tt/A.java:4: JML null initialization of non_null field oooo"
                ,"/tt/A.java:2: JML static initialization may not be correct: non-null static field has null value: o"
                ,"/tt/A.java:2: JML static initialization may not be correct: non-null static field has null value: oo"
                ,"/tt/A.java:4: JML static initialization may not be correct: non-null static field has null value: oooo"
                ,"/tt/A.java:6: JML null initialization of non_null field local"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:2: JML non-null field is null" // FIXME - add the name of the field
                ,"/tt/A.java:2: JML non-null field is null"
                ,"/tt/A.java:4: JML non-null field is null"
                );
    }
    
    @Test public void testNullDefault() {
        helpTCX("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}} class B { \n}"
                ,"/tt/A.java:3: JML null initialization of non_null field ooo"
                ,"/tt/A.java:3: JML static initialization may not be correct: non-null static field has null value: ooo"
                ,"/tt/A.java:6: JML non-null field is null"
                ,"/tt/A.java:7: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:3: JML non-null field is null"
                );
    }
    
    @Test public void testNullInit() {
        helpTCX("tt.A","package tt; public class A  { \n"
                +"/*@nullable*/ static Object o,oo = null; \n"
                +"static Object ooo = null;\n"
                +"//@ static invariant o != ooo;\n"
                +"//@ nullable ghost static Object oooo = null;\n"
                +"public static void main(String[] args) { \n"
                +"   /*@ nullable*/ String local = (String)ooo;\n"
                +"   //@ ghost String loc = null; \n"
                +"System.out.println(\"END\"); "
                +"}}"
                ,"/tt/A.java:3: JML null initialization of non_null field ooo"
                ,"/tt/A.java:3: JML static initialization may not be correct: non-null static field has null value: ooo"
                ,"/tt/A.java:1: JML static initialization may not be correct: invariant is false"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:7: JML non-null field is null"
                ,"/tt/A.java:8: JML null initialization of non_null field loc"
                ,"END"
                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:4: Associated declaration"
                ,"/tt/A.java:3: JML non-null field is null"
                );
    }
    
    // check readable, writable, monitors for
    // check modifiers?
    // check more method clauses
    // check other expression types
    // what about assignable
    // check any problems with grouped clauses
    @Test public void testNotImplemented() {
        main.addOptions("-keys=DEBUG");
        //print = true;
        expectedExit = 1;
        helpTCX("tt.A","package tt; public class A  { \n"
                +"//@ axiom true;\n"
                +"//@ public invariant \\duration(true) == 0;\n"
                +"//@ public model long i;\n"
                +"//@ public represents i =  \\duration(true);\n"
                +"//@ public constraint \\duration(true) == 0;\n"
                +"//@ public initially \\duration(true) == 0;\n"
                +"public static void main(String[] args) { \n"
                +"    //@ hence_by true; \n"
                +"    //@ assert \\duration(true) == 0;\n"
                +"    //@ assume \\duration(true) == 0;\n"
                +"    //@ ghost long k = \\duration(true);\n"
                +"    //@ set k = \\duration(true);\n"
                +"    //@ debug k = \\duration(true);\n"
                +"    System.out.println(\"END\"); "
                +"}\n"
                +"//@ ghost long z = \\duration(true);\n"
                +"//@ ghost long[] zz = { \\duration(true) } ;\n"
                +"/*@ requires \\duration(true) == 0;*/\n"
                +"int ma() { return 0; }\n"
                +"//@ ensures \\duration(true) == 0;\n"
                +"//@ signals (Exception ex) \\duration(true) == 0;\n"
                +"//@ signals_only RuntimeException;\n" 
                +"//@ diverges \\duration(true) == 0;\n" // line 23
                +"//@ duration  \\duration(true);\n"
                +"//@ working_space \\duration(true);\n"
                +"int mb() { return 0; }\n"
                +"}"
                ,"/tt/A.java:3: Note: Not implemented for runtime assertion checking: invariant clause containing \\duration",31
                ,"/tt/A.java:7: Note: Not implemented for runtime assertion checking: initially clause containing \\duration",31
                ,"/tt/A.java:9: Note: Not implemented for runtime assertion checking: hence_by statement",9
                ,"/tt/A.java:10: Note: Not implemented for runtime assertion checking: assert statement containing \\duration",25
                ,"/tt/A.java:11: Note: Not implemented for runtime assertion checking: assume statement containing \\duration",25
                ,"/tt/A.java:12: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",33
                ,"/tt/A.java:13: Note: Not implemented for runtime assertion checking: set statement containing \\duration",26
                ,"/tt/A.java:14: Note: Not implemented for runtime assertion checking: debug statement containing \\duration",28
                ,"/tt/A.java:16: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",29
                ,"/tt/A.java:17: Note: Not implemented for runtime assertion checking: ghost declaration containing \\duration",34
                ,"/tt/A.java:18: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",23
                ,"/tt/A.java:6: Note: Not implemented for runtime assertion checking: constraint clause containing \\duration",32
                ,"/tt/A.java:20: Note: Not implemented for runtime assertion checking: ensures clause containing \\duration",22
                ,"/tt/A.java:21: Note: Not implemented for runtime assertion checking: signals clause containing \\duration",37
                ,"/tt/A.java:23: Note: Not implemented for runtime assertion checking: diverges clause containing \\duration",23
                ,"/tt/A.java:24: Note: Not implemented for runtime assertion checking: duration clause containing \\duration",24
                ,"/tt/A.java:25: Note: Not implemented for runtime assertion checking: working_space clause containing \\duration",28
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: represents clause containing \\duration",37
                ,"/tt/A.java:5: Unrecoverable situation: Unimplemented construct in a method or model method or represents clause",37
                ,"END"
                );

    }
    
    @Test public void testNotImplemented2() {
        helpTCX("tt.A","package tt; public class A  { \n"
                +"public static void main(String[] args) { \n"
                +"    m();\n"
                +"    System.out.println(\"END\"); "
                +"}\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   ensures true;\n"
                +"//@ also\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   signals (Exception ex) true;\n"
                +"//@ also\n"
                +"//@   requires \\duration(true) == 0;\n"
                +"//@   signals_only RuntimeException;\n"
                +"//@ also\n"
                +"//@   ensures true;\n"
                +"static int m() { return 0; }\n"
                +"}"
                ,"/tt/A.java:5: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"/tt/A.java:8: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"/tt/A.java:11: Note: Not implemented for runtime assertion checking: requires clause containing \\duration",25
                ,"END"
                );
    }

    @Test public void testSuperInvariant() {
        helpTCX("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@public  invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                +"class B extends C { //@ public invariant i == 2; \n"
                +"}\n"
                +"class C { \n"  // Line 13
                +"  Object o = this; \n"
                +"  public int i=0; \n"
                +"  public void m() {} \n"
                +"  //@ public invariant i == 3; \n"
                +"}\n"   // FIXME - should check invariants on reentering caller after returning from super call
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in C, exiting B()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in B, exiting B()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in C, exiting A()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in B, exiting A()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()" // Invariant in A, exiting A()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in C, exiting caller
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in B, exiting caller
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])" // Invariant in A, exiting caller
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in C, entering m
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in C, entering m
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in C, entering m
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in C, entering m
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in B, entering m
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())" // Invariant in A, entering m
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()" // Invariant in C, beginning m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()" // Invariant in B, beginning m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()" // Invariant in A, beginning m()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in C, completing m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in B, completing m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()" // Invariant in A, completing m()
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in B, leaving m()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])" // Invariant in A, leaving m()
                ,"/tt/A.java:2: Associated declaration"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in C, exiting B()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:11: JML invariant is false on leaving method tt.B.B()" // Invariant in B, exiting B()
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:11: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())" // Invariant in C, entering m() - this is C.m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())" // Invariant in C, entering m() - this is C.m()
                ,"/tt/A.java:17: Associated declaration"
                // FIXME should be checking B's invariants as well, since the receiver is B, above
                ,"/tt/A.java:16: JML invariant is false on entering method tt.C.m()" // Invariant in C, beginning m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML invariant is false on leaving method tt.C.m()" // Invariant in C, completing m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])" // Invariant in C, exiting m()
                ,"/tt/A.java:17: Associated declaration"
                ,"MID"
                ,"/tt/A.java:13: JML invariant is false on leaving method tt.C.C()"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on leaving method tt.C.C(), returning to tt.A.main(java.lang.String[])"  // Invariant in C, exiting C()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/tt/A.java:17: Associated declaration"              
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())" // Invariant in C, entering m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML invariant is false on entering method tt.C.m()" // Invariant in C, entering m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:16: JML invariant is false on leaving method tt.C.m()" // Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])" // Invariant in C, leaving m()
                ,"/tt/A.java:17: Associated declaration"
                ,"END"
                );
    }

    // Testing inheritance of invariants; here m() is implemented for classes A and C, but not B
    @Test public void testSuperInvariantB() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ public invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"public int i=0; public void m() {} \n"
                +"//@ public invariant i == 3; \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends B { \n"
                +" public void m() {} //@public  invariant i == 1; \n"
                +"public static void main(String[] args) { \n"
                +"   new A().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new B().m(); \n"
                +"System.out.println(\"MID\"); \n"
                +"   new C().m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"  // FIXME _ review all these output messages against expected invariants
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"  // leaving C() in A(), invariant in C
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"  
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML invariant is false on leaving method tt.A.A()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.A(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on entering method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"

                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:2: JML invariant is false on leaving method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"

                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"MID"
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML invariant is false on leaving method tt.B.B()"
                ,"/$A/tt/B.java:2: Associated declaration"

                ,"/tt/A.java:6: JML invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.B.B(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"

                ,"/tt/A.java:6: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"

                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                
                ,"/$A/tt/C.java:2: JML invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"MID"
                ,"/$A/tt/C.java:1: JML invariant is false on leaving method tt.C.C()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on leaving method tt.C.C(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"END"
                );
    }

    @Test public void testStaticInhInvariant() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C { \n"
                +"//@ static public invariant i == 2; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"static public int i=0; static public void m() {} \n"
                +"//@ static public invariant i == 3; \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends tt.B { \n"
                +" //@ static public invariant i == 1; \n"
                +" static public void m() {}\n"
                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   A.m(); \n"
                +"System.out.println(\"B\"); \n"
                +"   tt.B.m(); \n"
                +"System.out.println(\"C\"); \n"
                +"   tt.C.m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"/$A/tt/C.java:1: JML static initialization may not be correct: invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML static initialization may not be correct: invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/B.java:1: JML static initialization may not be correct: invariant is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML static initialization may not be correct: invariant is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:1: JML static initialization may not be correct: invariant is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:1: JML static initialization may not be correct: invariant is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on entering method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"A"
                ,"/tt/A.java:5: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:5: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:5: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
//                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
//                ,"/$A/tt/C.java:3: Associated declaration"
//                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
//                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on entering method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML invariant is false on leaving method tt.A.m()"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML invariant is false on leaving method tt.A.m(), returning to tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.A.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"B"
                ,"/tt/A.java:7: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:7: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:7: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
//                ,"/tt/A.java:8: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
//                ,"/$A/tt/B.java:2: Associated declaration"
//                ,"/tt/A.java:8: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
//                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:8: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"C"
                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:9: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:10: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
//                ,"/tt/A.java:10: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
//                ,"/$A/tt/B.java:2: Associated declaration"
//                ,"/tt/A.java:10: JML caller invariant is false on leaving calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
//                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:10: JML invariant is false on entering method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on entering method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/$A/tt/C.java:2: JML invariant is false on leaving method tt.C.m()"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:10: JML invariant is false on leaving method tt.C.m(), returning to tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:10: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:10: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:10: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: tt.C.m())"
                ,"/tt/A.java:2: Associated declaration"
                ,"END"
                ,"/tt/A.java:11: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:11: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:11: JML caller invariant is false on reentering calling method (Caller: tt.A.main(java.lang.String[]), Callee: java.io.PrintStream.println(java.lang.String))"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:4: JML invariant is false on leaving method tt.A.main(java.lang.String[])"
                ,"/tt/A.java:2: Associated declaration"
                );
    }
    
    // FIXME - many outputs need column numbers

    @Test public void testInheritedMethod() {
        addMockFile("$A/tt/B.java","package tt; public class B extends tt.C implements I { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/C.java","package tt; public class C implements I { \n"
                +"static public int i=0;  \n"
                +"//@ also ensures i == 3; \n"
                +" public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/I.java","package tt; public interface I { \n"
                +"//@ ensures false; \n"
                +"public void m(); \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"

                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   (new A()).m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testInheritedMethod2() {
        addMockFile("$A/tt/B.java","package tt; public class B extends ttt.C implements I { \n"
                +"//@ also private behavior ensures i == 2; \n"
                +"public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/ttt/C.java","package ttt; public class C implements tt.I { \n"
                +"static public int i=0;  \n"
                +"//@ also ensures i == 3; \n"
                +" public void m() {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/I.java","package tt; public interface I { \n"
                +"//@ ensures false; \n"
                +"public void m(); \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also ensures i == 2; \n"
                +"public void m() {} ; \n"

                +"public static void main(String[] args) { \n"
                +"System.out.println(\"A\"); \n"
                +"   (new A()).m(); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/ttt/C.java:3: Associated declaration"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/I.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/ttt/C.java:3: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"END"
                );
    }
    
    @Test public void testInheritedMethod3() {
        addMockFile("$A/tt/C.java","package tt; public class C { \n"
                +"static public int i=0;  \n"
                +"//@ requires kc == 3; ensures i == 3; \n"
                +" public void m(int kc) {} ; \n"
                +"}\n"
                );
        addMockFile("$A/tt/B.java","package tt; public class B extends C { \n"
                +"//@ also requires kb == 2; ensures i == 2; \n"
                +"public void m(int kb) {} ; \n"
                +"}\n"
                );
        helpTCX("tt.A","package tt; public class A  extends tt.B { \n"
                +"//@ also requires ka==1; ensures i == 1; \n"
                +"public void m(int ka) {} ; \n"

                +"public static void main(String[] args) { \n"
                +"   System.out.println(\"C\"); (new A()).m(3); \n"
                +"   System.out.println(\"B\"); (new A()).m(2); \n"
                +"   System.out.println(\"A\"); (new A()).m(1); \n"
                +"   System.out.println(\"NONE\"); (new A()).m(0); \n"
                +"System.out.println(\"END\"); \n"
                +"}} \n"
                ,"C"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"/tt/A.java:5: JML postcondition is false"
                ,"/$A/tt/C.java:3: Associated declaration"
                ,"B"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"/tt/A.java:6: JML postcondition is false"
                ,"/$A/tt/B.java:2: Associated declaration"
                ,"A"
                ,"/tt/A.java:3: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"/tt/A.java:7: JML postcondition is false"
                ,"/tt/A.java:2: Associated declaration"
                ,"NONE"
                ,"/tt/A.java:8: JML precondition is false"
                ,"/tt/A.java:3: Associated declaration"
                ,"/tt/A.java:2: JML precondition is false"
                ,"END"
                );
    }
    
    @Test public void testAssignable() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    j = i;\n"
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(0);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:11: JML precondition is false"
                ,"/tt/A.java:6: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Test public void testAssignable2() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies j;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    k = i;\n" // Intentionally k - but precondition is false, so does not violate the assignable clause
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(0);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:11: JML precondition is false"
                ,"/tt/A.java:6: Associated declaration"
                ,"/tt/A.java:3: JML precondition is false"
                ,"/tt/A.java:10: JML postcondition is false"
                ,"/tt/A.java:9: Associated declaration"
        );
    }
    
    @Ignore    // FIXME - assignable turned off for RAC, until we can decide fresh allocations
    @Test public void testAssignable3() {
        helpTCX("tt.A","package tt; public class A {\n"
                +"  static public int j=0,k;\n"
                +"  //@ requires i > 0;\n"
                +"  //@ modifies k;\n"
                +"  //@ ensures j == i;\n"
                +"  public static void setj(int i) {\n"
                +"    j = i;\n" 
                +"  }\n"
                +"  //@ ensures j == 1;\n"
                +"  public static void main(String[] args) {\n"
                +"    setj(1);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/A.java:7: JML An item is assigned that is not in the assignable statement: .tt.A.j"
                ,"/tt/A.java:4: Associated declaration" // FIXME - this does not make sense
        );
    }
    
    @Test public void testLabelledStatement() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == 0; */ \n System.out.println(\"END\"); }}"
                ,"END");
    }

    @Test public void testLabelledStatement2() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i=5; \n outer: while (i > 0)  { --i; } \n /*@ assert i == -1; */ }}"
                ,"/tt/A.java:4: JML assertion is false"
                );
    }

    @Test public void testInitializer() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) {  }\n { //@ assert false; \n } " +
                "}"
                ); // The assert is not executed
    }

    @Test public void testInitializer2() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n {  //@ assert false; \n  \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false"
                ,"END");
    }

    @Test public void testInitializer2a() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) { A a = new A(); System.out.println(\"END\"); }\n  " +
                "}"
                ,"END");
    }

    @Test public void testInitializer3() {
        helpTCX("tt.A","package tt; public class A { public static void main(String[] args) {  }\n static { //@ assert false; \n } " +
                "}"
                ,"/tt/A.java:2: JML assertion is false");
    }

    @Test
    public void testChangedParam() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == i;\n"
                +"  public static int m1bad(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i+1;\n"
                +"  public static int m1good(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  public static void main(String ... args) {\n"
                +"    m1good(2);\n"
                +"    m1bad(4);\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:4: JML postcondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:13: JML postcondition is false"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }

    @Test public void testSynchronized() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { new A().m(); }\n public void m() { int i; \n synchronized (this) { i = 0; } \n}}"
                );
    }

    @Test public void testForEach3() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list); }"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForEach3bad() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list);}"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }

    @Test public void testForEach4() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{1,2,3}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForEach4bad() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{0,0,0}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }
    
    
    @Test
    public void testOldClause() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { public static void main(String[] args) { m(6); k = 6; m(6); } \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k; requires i > kk; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n"
                + "  //@ old int kkk = k+1; requires i < kkk; assignable k; ensures k == i-1; ensures kkk == 7;\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testOldClause1() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { public static void main(String[] args) { m(6); k = 6; m(6); } \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k; requires i > kk; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n" // Purposely duplicating the name of the old variable
                + "  //@ old int kk = k+1; requires i < kk; assignable k; ensures k == i-1; ensures kk == 7;\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testOldClause2() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { public static void main(String[] args) { m(6); k = 6; m(4); } \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k;\n"
                + "  //@ {| requires i > kk; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n"
                + "  //@    requires i < kk; assignable k; ensures k == i-1; ensures kk == 6;\n"
                + "  //@ |}\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testShowStatement() {
        expectedExit = 0;
        main.addOptions("-code-math=bigint","-method=m");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static void main(String[] args) { m(3,-8); } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i, j+1;\n"
                        + "     int k = i+j;\n"
                        + "     //@ show k;\n"
                        + "     //@ assert k > 0;\n"
                        + "     int m = i-j;\n"
                        + "     //@ show m,k;\n"
                        + "     //@ assert m > 0;\n"
                        + "  }\n"
                        + "}\n"
                        ,"LABEL JMLSHOW_1 = 3"
                        ,"LABEL JMLSHOW_2 = -7"
                        ,"LABEL JMLSHOW_3 = -5"
                        ,"/tt/TestJava.java:10: JML assertion is false"
                        ,"LABEL JMLSHOW_4 = 11"
                        ,"LABEL JMLSHOW_5 = -5"
                        );
    }



}
