package org.jmlspecs.openjmltest.testcases;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

// These tests are run for both new and custom translations.

/** These tests check the RAC functionality of outputting a stack trace along with
 * notification of failed RAC assertions.  These test that library class files 
 * recompiled with RAC actually get used and produce errors.  Hence the need to 
 * put the new system classes (in jdkbin) in the bootclasspath ahead of the regular
 * java classes.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racsystem extends RacBase {

//    String option;
//    
//    public racsystem(String o) {
//        option = o;
//    }
//
    
    /** The command-line to use to run RACed programs - note the inclusion of the
     * RAC-compiled JDK library classes ahead of the regular Java libaray classes
     * in the boot class path. (This may not work on all platforms)
     */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        jdkrac = true;
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-no-purityCheck"); // To shut off complaints about misuse of purity in Java specifications
    }
    
    @Override
    public void tearDown() throws Exception {
        System.clearProperty("org.jmlspecs.openjml.racexitcode");
    }

    /** Testing with getting a stack trace */
    @Test @Ignore    // FIXME - not testing rac-compiled JDK files
    public void testFile2() {
        expectedRACExit = 1; 
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); } \n"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"Exception in thread \"main\" org.jmlspecs.utils.JmlAssertionError: File.refines-spec:77: JML precondition is false"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:63)"
                ,"\tat java.io.File.compareTo(File.java:2093)"
                ,"\tat tt.TestJava.m(TestJava.java:6)"
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                );
    }

    /** Testing with getting a stack trace - Exception does not catch it */
    @Test
    public void testFile2a() {
        expectedRACExit = 1;
        main.addOptions("-no-racShowSource","-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { System.out.println(\"CAUGHT ASSERTION\"); e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); } \n"
                +"/*@ signals (Exception e) false;*/ \n"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"Exception in thread \"main\" org.jmlspecs.utils.JmlAssertionError: /tt/TestJava.java:6: JML signals condition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"\tat org.jmlspecs.utils.Utils.createException(Utils.java:103)"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:55)"
                ,"\tat tt.TestJava.m(TestJava.java:1)" // FIXME - should be line 6
                ,"\tat tt.TestJava.main(TestJava.java:3)"       
                );
    }

    /** Testing with getting a stack trace - Exception does not catch it */
    @Test
    public void testFile2pre() {
        expectedRACExit = 1;
        main.addOptions("-no-racShowSource","-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Exception e) { System.out.println(\"CAUGHT ASSERTION\"); e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); } \n"
                +"/*@ requires false;*/ \n"
                +"static public void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"Exception in thread \"main\" org.jmlspecs.utils.JmlAssertionError$Precondition: /tt/TestJava.java:3: JML precondition is false"
                ,"/tt/TestJava.java:6: Associated declaration"
                ,"\tat org.jmlspecs.utils.Utils.createException(Utils.java:87)"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:55)"
                ,"\tat tt.TestJava.main(TestJava.java:1)"         // FIXME - should be line 3   
                );
    }

    /** Testing with getting a stack trace - Error does catch it */
    @Test
    public void testFile2c() {
        expectedRACExit = 0;
        main.addOptions("-no-racShowSource","-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.useExceptions = true; \n"
                +"try { m(); } catch (Error e) { System.out.println(\"CAUGHT ASSERTION\"); e.printStackTrace(System.out); } \n"
                +"System.out.println(\"END\"); }\n"
                +"/*@ signals (Exception e) false;*/ \n"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                
                ,"CAUGHT ASSERTION"
                ,"org.jmlspecs.utils.JmlAssertionError: /tt/TestJava.java:6: JML signals condition is false"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"\tat org.jmlspecs.utils.Utils.createException(Utils.java:103)"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:55)"
                ,"\tat tt.TestJava.m(TestJava.java:1)" // FIXME - nshould be line 6
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"END"
                );
    }
    

    /** Testing with getting a stack trace using showStack */
    @Test
    public void testFile2d() {
        expectedRACExit = 0;
        expectedNotes = 0;
        main.addOptions("-no-internalSpecs");
        main.addOptions("-no-racShowSource");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"m();\n"
                +"System.out.println(\"END\"); }\n"
                +"static void m() {\n"
                +"  //@ assert false;\n"
                +"}"
                +"}"
                
                ,"/tt/TestJava.java:6: JML assertion is false"
                ,"org.jmlspecs.utils.JmlAssertionError: /tt/TestJava.java:6: JML assertion is false"
                ,"\tat org.jmlspecs.utils.Utils.createException(Utils.java:103)"
                ,"\tat org.jmlspecs.utils.Utils.assertionFailureL(Utils.java:61)"
                ,"\tat tt.TestJava.m(TestJava.java:1)" // FIXME - should be line 6
                ,"\tat tt.TestJava.main(TestJava.java:3)"
                ,"END"
                );
    }
    
    /** Testing with an exit code */
    @Test
    public void testFile2e() {
        expectedRACExit = 5;
        expectedNotes = 0;
        rac = new String[]{jdk, "-Dorg.jmlspecs.openjml.racexitcode=5", "-ea", "-classpath","../OpenJML/bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"m();\n"
                +"System.out.println(\"END\"); }\n"
                +"static void m() {\n"
                +"  //@ assert false;\n"
                +"}"
                +"}"
                
                ,"/tt/TestJava.java:5: JML assertion is false"
                ,"END"
                ,"1 verification error"
                );
    }
    
    @Test
    public void testFile3() {
        expectedNotes =  0; // 2
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"try { m(); } catch (Exception e) { System.out.println(\"CAUGHT EXCEPTION\"); } \n"
                +"System.out.println(\"END\"); }\n"
                +"//@ signals_only Exception;\n"
                +"static void m() {\n"
                +"  int i = (new java.io.File(\"A\")).compareTo((java.io.File)null);\n"
                +"}"
                +"}"
                ,"CAUGHT EXCEPTION"
                ,"END"
                );
    }
    
    @Test
    public void testHashCode() {
        expectedNotes =  0; // 2
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n"
                +"org.jmlspecs.utils.Utils.showStack = true; \n"
                +"int i = ( new Object().hashCode()); \n"
                +"int j = ( new Object().hashCode()); \n"
                +" System.out.println(i==j);"
                +"System.out.println(\"END\"); }"
                +"}"
                ,"false"
                ,"END"
                );
    }
    
    /** This tests a bug in which matching with no specs file to a main
     * routine with String... did not work.  Here we use String[] which
     * did work.
     */
    @Test
    public void testMain() {
        expectedNotes = 2;
        main.addOptions("-no-racShowSource");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
                +"public static void main(String[] args) { \n"
                +"  System.out.println(\"START\"); \n"
                +"  //@ assert args.length != 0;\n"
                +"  System.out.println(\"END\"); }"
                +"}"
                ,"START"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"END"
                );
    }
    
    /** This tests a bug in which matching with no specs file to a main
     * routine with String... did not work.  
     */
    @Test
    public void testMain2() {
        expectedNotes = 0;
        main.addOptions("-no-internalSpecs");
        main.addOptions("-no-racShowSource");
        helpTCX("tt.TestJava","package tt; public class TestJava { \n"
                +"public static void main(String... args) { \n"
                +"  System.out.println(\"START\"); \n"
                +"  //@ assert args.length != 0;\n"
                +"  System.out.println(\"END\"); }"
                +"}"
                ,"START"
                ,"/tt/TestJava.java:4: JML assertion is false"
                ,"END"
                );
    }
    

}
