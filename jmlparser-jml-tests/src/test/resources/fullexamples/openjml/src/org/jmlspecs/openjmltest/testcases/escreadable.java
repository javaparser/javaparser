package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escreadable extends EscBase {

    public escreadable(String option, String solver) {
        super(option,solver);
    }
        
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //main.addOptions("-jmlverbose");
        //main.addOptions("-method",   "m2bad");
        //main.addOptions("-jmldebug");
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    // FIXME - needs writable checks for assignables in method calls?
    // FIXME - what about assignments to arrays elements
    // FIXME - what about references in type decl initializations
    // FIXME - what about reads/writes in constructors
    // FIXME - same checks in rac

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


                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Readable-if) in method m1b:  tt.TestJava.x",12
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Readable-if) in method m1c:  tt.TestJava.x",16
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Readable-if) in method m2b:  tt.TestJava.y",12
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Readable-if) in method m2c:  tt.TestJava.y",20
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Readable-if) in method m3b:  tt.TestJava.z",13
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:40: warning: The prover cannot establish an assertion (Readable-if) in method m3c:  tt.TestJava.z",16
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:48: warning: The prover cannot establish an assertion (Readable-if) in method m3e:  tt.TestJava.z",12
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
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

                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Writable-if) in method m1b:  tt.TestJava.x",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Writable-if) in method m1c:  tt.TestJava.x",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Writable-if) in method m2b:  tt.TestJava.y",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Writable-if) in method m2c:  tt.TestJava.y",13
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:38: warning: The prover cannot establish an assertion (Writable-if) in method m3b:  tt.TestJava.z",6
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (Writable-if) in method m3c:  tt.TestJava.z",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:50: warning: The prover cannot establish an assertion (Writable-if) in method m3e:  tt.TestJava.z",9
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                );
    }

    @Test
    public void testWritable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean b; public boolean bb; int z; //@ writable z if bb; \n"
                +"  int x; //@ writable x if b; \n"
                +"  static int y; //@ writable y if b; \n"

                +"  //@ requires b; \n"
                +"  public void m1(int i) {\n"
                +"    x += 0 ; i += 0; int j = 0; j += 0;\n"
                +"    this.x += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1b() {\n"
                +"    x += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1c() {\n"
                +"    this.x += 0 ;\n"
                +"  }\n"

                +"  //@ requires b; \n"
                +"  public void m2() {\n"
                +"    y += 0;\n"
                +"    TestJava.y += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2b() {\n"
                +"    y += 0;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2c() {\n"
                +"    TestJava.y += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3(TestJava a) {\n"
                +"    a.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3b(TestJava a) {\n"
                +"    a.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3c(TestJava a) {\n"
                +"    z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3d(TestJava a) {\n"
                +"    z += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3e(TestJava a) {\n"
                +"    this.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3f(TestJava a) {\n"
                +"    this.z += 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Writable-if) in method m1b:  tt.TestJava.x",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Writable-if) in method m1c:  tt.TestJava.x",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Writable-if) in method m2b:  tt.TestJava.y",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Writable-if) in method m2c:  tt.TestJava.y",13
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:38: warning: The prover cannot establish an assertion (Writable-if) in method m3b:  tt.TestJava.z",6
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (Writable-if) in method m3c:  tt.TestJava.z",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:50: warning: The prover cannot establish an assertion (Writable-if) in method m3e:  tt.TestJava.z",9
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                );
    }

    @Test
    public void testReadableA() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean b; public boolean bb; int z; //@ readable z if bb; \n"
                +"  int x; //@ readable x if b; \n"
                +"  static int y; //@ readable y if b; \n"

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

                +"}"
                );
    }

    @Test
    public void testReadableB() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean b; public boolean bb; int z; //@ readable z if bb; \n"
                +"  int x; //@ readable x if b; \n"
                +"  static int y; //@ readable y if b; \n"

                +"  //@ requires b; \n"
                +"  public void m1(int i) {\n"
                +"    x += 0 ; i += 0; int j = 0; j += 0;\n"
                +"    this.x += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1b() {\n"
                +"    x += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m1c() {\n"
                +"    this.x += 0 ;\n"
                +"  }\n"

                +"  //@ requires b; \n"
                +"  public void m2() {\n"
                +"    y += 0;\n"
                +"    TestJava.y += 0 ;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2b() {\n"
                +"    y += 0;\n"
                +"  }\n"

                +"  //@ requires !b; \n"
                +"  public void m2c() {\n"
                +"    TestJava.y += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3(TestJava a) {\n"
                +"    a.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3b(TestJava a) {\n"
                +"    a.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3c(TestJava a) {\n"
                +"    z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3d(TestJava a) {\n"
                +"    z += 0 ;\n"
                +"  }\n"

                +"  //@ requires !bb && a.bb; \n"
                +"  public void m3e(TestJava a) {\n"
                +"    this.z += 0 ;\n"
                +"  }\n"

                +"  //@ requires bb && !a.bb; \n"
                +"  public void m3f(TestJava a) {\n"
                +"    this.z += 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Readable-if) in method m1b:  tt.TestJava.x",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Readable-if) in method m1c:  tt.TestJava.x",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Readable-if) in method m2b:  tt.TestJava.y",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Readable-if) in method m2c:  tt.TestJava.y",13
                ,"/tt/TestJava.java:5: warning: Associated declaration",21
                ,"/tt/TestJava.java:38: warning: The prover cannot establish an assertion (Readable-if) in method m3b:  tt.TestJava.z",6
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (Readable-if) in method m3c:  tt.TestJava.z",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                ,"/tt/TestJava.java:50: warning: The prover cannot establish an assertion (Readable-if) in method m3e:  tt.TestJava.z",9
                ,"/tt/TestJava.java:3: warning: Associated declaration",58
                );
    }

    @Test
    public void testVisibility() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math*/ public class TestJava { \n"
                +"  public static boolean bs1;\n"
                +"  protected static boolean bs2;\n"
                +"   static boolean bs3;\n"
                +"  private static boolean bs4;\n"
                +"  public boolean b1;\n"
                +"  protected boolean b2;\n"
                +"   boolean b3;\n"
                +"  private boolean b4;\n"
                
                +"  static public int z1; //@ readable z1 if b1; \n"
                +"  public int x1; //@ readable x1 if b1 || b2 || b3 || b4; \n"
                +"  static public int y1; //@ readable y1 if bs1 || bs2 || bs3 || bs4; \n"
                +"  protected int x2; //@ readable x2 if b1 || b2 || b3 || b4; \n"
                +"  static protected int y2; //@ readable y2 if bs1 || bs2 || bs3 || bs4; \n"
                +"   int x3; //@ readable x3 if b1 || b2 || b3 || b4; \n"
                +"  static  int y3; //@ readable y3 if bs1 || bs2 || bs3 || bs4; \n"
                +"  private int x4; //@ readable x4 if b1 || b2 || b3 || b4; \n"
                +"  static private int y4; //@ readable y4 if bs1 || bs2 || bs3 || bs4; \n"

                +"}"
                ,"/tt/TestJava.java:11: non-static variable b1 cannot be referenced from a static context",44
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a readable clause with public visibility",43
                ,"/tt/TestJava.java:12: An identifier with package visibility may not be used in a readable clause with public visibility",49
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a readable clause with public visibility",55
                ,"/tt/TestJava.java:13: An identifier with protected visibility may not be used in a readable clause with public visibility",51
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a readable clause with public visibility",58
                ,"/tt/TestJava.java:13: An identifier with private visibility may not be used in a readable clause with public visibility",65
                ,"/tt/TestJava.java:14: An identifier with package visibility may not be used in a readable clause with protected visibility",52
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a readable clause with protected visibility",58
                ,"/tt/TestJava.java:15: An identifier with package visibility may not be used in a readable clause with protected visibility",61
                ,"/tt/TestJava.java:15: An identifier with private visibility may not be used in a readable clause with protected visibility",68
                ,"/tt/TestJava.java:16: An identifier with private visibility may not be used in a readable clause with package visibility",49
                ,"/tt/TestJava.java:17: An identifier with private visibility may not be used in a readable clause with package visibility",59
                );
    }


}
