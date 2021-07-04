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
public class racreadable extends RacBase {

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
    public void testReadable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean b; public boolean bb; int z; //@ readable z if bb; \n"
                +"  int x; //@ readable x if b; \n"
                +"  static int y; //@ readable y if b; \n"

                +"  //@ requires b; \n"
                +"  public int m1(int i) { int j = 0; \n"
                +"    return x + this.x + i + j;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public int m1b() {\n"
                +"    return x;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public int m1c() {\n"
                +"    return this.x ;\n"
                +"  }\n"

                +"  //@ requires b; \n"
                +"  public int m2() {\n"
                +"    return y + TestJava.y ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public int m2b() {\n"
                +"    return y;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public int m2c() {\n"
                +"    return TestJava.y ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public int m3(TestJava a) {\n"
                +"    return a.z ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public int m3b(TestJava a) {\n"
                +"    return a.z ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public int m3c(TestJava a) {\n"
                +"    return this.z ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public int m3d(TestJava a) {\n"
                +"    return this.z ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public int m3e(TestJava a) {\n"
                +"    return z ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public int m3f(TestJava a) {\n"
                +"    return z ;\n"
                +"  }\n"

                +"  public static void main(String... args) { \n"
                +"     TestJava a = new TestJava(); TestJava t = new TestJava(); \n"
                +"     t.b = true; t.m1(0); t.b = false; t.m1b(); t.m1c(); \n"
                +"     t.b = true; t.m2(); t.b = false; t.m2b(); t.m2c(); \n"
                +"     t.bb = false; a.bb = true; t.m3(a); \n"
                +"     t.bb = true; a.bb = false; t.m3b(a); \n"
                +"     t.bb = false; a.bb = true; t.m3c(a); \n"
                +"     t.bb = true; a.bb = false; t.m3d(a); \n"
                +"     t.bb = false; a.bb = true; t.m3e(a); \n"
                +"     t.bb = true; a.bb = false; t.m3f(a); \n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:12: JML readable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:16: JML readable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:24: JML readable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:28: JML readable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:36: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:40: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:48: JML readable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }

    @Test
    public void testWritable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean b; public boolean bb; int z; //@ writable z if bb; \n"
                +"  int x; //@ writable x if b; \n"
                +"  static int y; //@ writable y if b; \n"

                +"  //@ requires b; \n"
                +"  public void m1(int i) {\n"
                +"    x = 0 ; i = 0; int j; j = 0;\n"
                +"    this.x = 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1b() {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1c() {\n"
                +"    this.x = 0 ;\n"
                +"  }\n"

                +"  //@ requires b; \n"
                +"  public void m2() {\n"
                +"    y = 0;\n"
                +"    TestJava.y = 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2b() {\n"
                +"    y = 0;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2c() {\n"
                +"    TestJava.y = 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3(TestJava a) {\n"
                +"    a.z = 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3b(TestJava a) {\n"
                +"    a.z = 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3c(TestJava a) {\n"
                +"    z = 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3d(TestJava a) {\n"
                +"    z = 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3e(TestJava a) {\n"
                +"    this.z = 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3f(TestJava a) {\n"
                +"    this.z = 0 ;\n"
                +"  }\n"

                +"  public static void main(String... args) { \n"
                +"     TestJava a = new TestJava(); TestJava t = new TestJava(); \n"
                +"     t.b = true; t.m1(0); t.b = false; t.m1b(); t.m1c(); \n"
                +"     t.b = true; t.m2(); t.b = false; t.m2b(); t.m2c(); \n"
                +"     t.bb = false; a.bb = true; t.m3(a); \n"
                +"     t.bb = true; a.bb = false; t.m3b(a); \n"
                +"     t.bb = false; a.bb = true; t.m3c(a); \n"
                +"     t.bb = true; a.bb = false; t.m3d(a); \n"
                +"     t.bb = false; a.bb = true; t.m3e(a); \n"
                +"     t.bb = true; a.bb = false; t.m3f(a); \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:13: JML writable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:17: JML writable clause is false for variable tt.TestJava.x"
                ,"/tt/TestJava.java:4: Associated declaration"
                ,"/tt/TestJava.java:26: JML writable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:30: JML writable clause is false for variable tt.TestJava.y"
                ,"/tt/TestJava.java:5: Associated declaration"
                ,"/tt/TestJava.java:38: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:42: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                ,"/tt/TestJava.java:50: JML writable clause is false for variable tt.TestJava.z"
                ,"/tt/TestJava.java:3: Associated declaration"
                );
    }


}
