package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racJML extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+z+"$SS";
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness=4");
        expectedNotes = 0;
        main.addOptions("-jmltesting");
    }

    @Test
    public void testLBLObject() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",\"Z\") != null; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = Z"
                );
    }

    @Test
    public void testLBLString() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",\"XYZ\").equals(\"XYZ\"); \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = XYZ"
                );
    }

    @Test
    public void testLBLboolean() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",args.length == 0); \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = true"
                );
    }

    @Test
    public void testLBLint() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLlong() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(long)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLshort() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(short)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLbyte() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",(byte)args.length) == 0; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = 0"
                );
    }

    @Test
    public void testLBLchar() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static void main(String... args) { \n"
                +"     //@ assert JML.lbl(\"AL\",'Z') == 'Z'; \n"
                +"  }\n"
                +"}"
                ,"LABEL AL = Z"
                );
    }

    @Test
    public void testLBLdouble() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //  @ ensures (\\lbl INPUTX i) == \\result;\n"
                +"  //@ ensures JML.lbl(\"INPUT\",i) == \\result;\n"
                +"  public static double m(double i) { return i; }\n"
                +"  public static void main(String... args) { "
                +"     //@ assert JML.lbl(\"AL\",5.0) != 0.0; }\n"
                +"}"
                ,"LABEL AL = 5.0"
                );
    }


}
