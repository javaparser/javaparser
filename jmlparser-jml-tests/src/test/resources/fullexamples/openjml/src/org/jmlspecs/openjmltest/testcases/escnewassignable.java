package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnewassignable extends EscBase {

    // Forms to test: x, this.x, , this.*
    // xx, T.xx, tt.T.x, T.* tt.T.*
    // o.x o.oo.x, m(o).x o.*, o.oo.*, m(o).* 
    // a[i].x a[i].* a[*].x a[*].* a[i .. j].x a[i ..*].x a[*..j].x a[*..*].x a[i .. j].* a[i ..*].* a[*..j].* a[*..*].*
    // a[i] a[i..j] a[*] a[i..*] a[*..j] a[*..*]
    // \everything \nothing \not_specified
    
    public escnewassignable(String options, String solver) {
        super(options,solver);
    }

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //print = true;
    }

    @Test
    public void testAssignable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x,y; \n"

                +"  //@ assignable x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"    i = 0; ;\n"
                +"    int k = 0; ;\n"
                +"    k = 0; ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void mgood(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"
                +"  }\n"

                +"}"
                );
    }

    @Test
    public void testAssignable3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x,y; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1good(int i) {\n"
                +"    if (i > 0) x = 0 ;\n"
                +"    if (i == 0) y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  x",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x,y; \n"

                +"  //@ requires i > 0; \n"
                +"  //@ assignable x; \n"
                +"  //@ also \n"
                +"  //@ requires i == 0; \n"
                +"  //@ assignable y; \n"
                +"  public void m1bad(int i) {\n"
                +"    i = 0 ;\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable5() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x,xx; public static int y,yy; \n"

                +"  //@ assignable this.x; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m2bad(int i) {\n"
                +"    xx = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m3bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m4bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m5bad(int i) {\n"
                +"    yy = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m6bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.y; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.y; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad:  xx",8
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad:  yy",8
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assignable) in method m4bad:  x",7
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assignable) in method m5bad:  yy",8
                ,"/tt/TestJava.java:20: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assignable) in method m6bad:  x",7
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable6() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int x,xx; static public int y,yy; \n"

                +"  //@ assignable this.*; \n"
                +"  public void m1bad(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.*; \n"
                +"  public void m2bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable this.*; \n"
                +"  public void m1good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ assignable TestJava.*; \n"
                +"  public void m2good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.*; \n"
                +"  public void m3good(int i) {\n"
                +"    y = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"
                +"  //@ assignable y; \n"
                +"  //@ also requires true; \n"
                +"  //@ assignable this.*; \n"
                +"  public void m0bad(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"  // TODO check that the semantics of JML is that assignable clauses may be split like this
                +"  //@ assignable y; \n"
                +"  //@ assignable this.*; \n"
                +"  public void m0good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"  //@ requires true; \n"
                +"  //@ assignable y, this.*; \n"
                +"  public void m00good(int i) {\n"
                +"    x = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assignable) in method m2bad:  x",7
                ,"/tt/TestJava.java:8: warning: Associated declaration",7
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m3bad:  x",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:33: warning: The prover cannot establish an assertion (Assignable) in method m0bad:  x",7
                ,"/tt/TestJava.java:29: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignable7() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; /*@ spec_public */ int[] z;\n"

                +"  //@ assignable \\everything; \n"
                +"  public void m1good(int i, TestJava a) {\n"
                +"    y = 0 ;\n"
                +"    x = 0 ;\n"
                +"    i = 0 ;\n"
                +"    this.x = 0 ;\n"
                +"    this.y = 0 ;\n"
                +"    a.x = 0 ;\n"
                +"    a.y = 0 ;\n"
                +"    TestJava.y = 0 ;\n"
                +"    //@ assume z != null && z.length > 1;\n"
                +"    z[0] = 0 ;\n"
                +"  }\n"

                +"  //@ assignable \\nothing; \n"
                +"  public void m1bad(int i, TestJava a) {\n"
                +"    y = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m2bad(int i, TestJava a) {\n"
                +"    x = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m3good(int i, TestJava a) {\n"
                +"    i = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m4bad(int i, TestJava a) {\n"
                +"    this.x = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m5bad(int i, TestJava a) {\n"
                +"    this.y = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m6bad(int i, TestJava a) {\n"
                +"    a.x = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m7bad(int i, TestJava a) {\n"
                +"    a.y = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m8bad(int i, TestJava a) {\n"
                +"    TestJava.y = 0 ;\n"
                +"  }\n"
                +"\n"
                +"  //@ assignable \\nothing; \n"
                +"  public void m9bad(int i, TestJava a) {\n"
                +"    //@ assume z != null && z.length > 1;\n"
                +"    z[0] = 0 ;\n"
                +"  }\n"

                +"  public TestJava() { z = new int[10];}\n"
                +"}"
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  y",7
                ,"/tt/TestJava.java:17: warning: Associated declaration",7
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Assignable) in method m2bad:  x",7
                ,"/tt/TestJava.java:22: warning: Associated declaration",7
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (Assignable) in method m4bad:  this.x",12
                ,"/tt/TestJava.java:32: warning: Associated declaration",7
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (Assignable) in method m5bad:  this.y",12
                ,"/tt/TestJava.java:37: warning: Associated declaration",7
                ,"/tt/TestJava.java:44: warning: The prover cannot establish an assertion (Assignable) in method m6bad:  a.x",9
                ,"/tt/TestJava.java:42: warning: Associated declaration",7
                ,"/tt/TestJava.java:49: warning: The prover cannot establish an assertion (Assignable) in method m7bad:  a.y",9
                ,"/tt/TestJava.java:47: warning: Associated declaration",7
                ,"/tt/TestJava.java:54: warning: The prover cannot establish an assertion (Assignable) in method m8bad:  TestJava.y",16
                ,"/tt/TestJava.java:52: warning: Associated declaration",7
                ,"/tt/TestJava.java:60: warning: The prover cannot establish an assertion (Assignable) in method m9bad:  z[0]",10
                ,"/tt/TestJava.java:57: warning: Associated declaration",7
                );
    }


    @Test
    public void testAssignable8() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int[] z;\n"
                +"  //@ public invariant z != null && z.length > 10;\n"
                
                +"  //@ requires a != null && a.length > 10; assignable a[1]; \n"
                +"  public void m1good(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable z[1]; \n"
                +"  public void m1bad(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[*]; \n"
                +"  public void m2good(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable z[*]; \n"
                +"  public void m2bad(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[0..3]; \n"
                +"  public void m3good(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable z[0..3]; \n"
                +"  public void m3bad(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[2..3]; \n"
                +"  public void m3bad1(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[0..0]; \n"
                +"  public void m3bad2(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[0..*]; \n"
                +"  public void m4good(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable z[0..*]; \n"
                +"  public void m4bad(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"  //@ requires a != null && a.length > 10; assignable a[2..*]; \n"
                +"  public void m4bad1(int i, int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"

                +"}"
                ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",8
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  a[1]",10
                ,"/tt/TestJava.java:9: warning: Associated declaration",44
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assignable) in method m2bad:  a[1]",10
                ,"/tt/TestJava.java:17: warning: Associated declaration",44
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assignable) in method m3bad:  a[1]",10
                ,"/tt/TestJava.java:25: warning: Associated declaration",44
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (Assignable) in method m3bad1:  a[1]",10
                ,"/tt/TestJava.java:29: warning: Associated declaration",44
                ,"/tt/TestJava.java:35: warning: The prover cannot establish an assertion (Assignable) in method m3bad2:  a[1]",10
                ,"/tt/TestJava.java:33: warning: Associated declaration",44
                ,"/tt/TestJava.java:43: warning: The prover cannot establish an assertion (Assignable) in method m4bad:  a[1]",10
                ,"/tt/TestJava.java:41: warning: Associated declaration",44
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (Assignable) in method m4bad1:  a[1]",10
                ,"/tt/TestJava.java:45: warning: Associated declaration",44
                );
    }

    @Test
    public void testAssignable9() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int i; static public int si; @org.jmlspecs.annotation.NonNull public TestJava b;\n"

                +"  //@ assignable a.i; \n"
                +"  public void m1good(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ assignable a.*; \n"
                +"  public void m2good(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ assignable b.i; \n"
                +"  public void m1bad(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ assignable b.*; \n"
                +"  public void m2bad(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ assignable a.si; \n"
                +"  public void m3bad(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ requires a == b; assignable b.i; \n"
                +"  public void m4good(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                +"  //@ requires a == this; assignable i; \n"
                +"  public void m5good(TestJava a) {\n"
                +"    a.i = 0 ;\n"
                +"  }\n"

                //FIXME - is this really no legal syntax
//              +"  //@ assignable *.i; \n"
//              +"  public void m3good(TestJava a) {\n"
//              +"    a.i = 0 ;\n"
//              +"  }\n"

                +"  public TestJava() { b = new TestJava(); } \n"
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  a.i",9
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assignable) in method m2bad:  a.i",9
                ,"/tt/TestJava.java:16: warning: Associated declaration",7
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assignable) in method m3bad:  a.i",9
                ,"/tt/TestJava.java:20: warning: Associated declaration",7
                );
    }

    @Test 
    public void testAssignableM1() {
//        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { public int x,y; public static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"

                +"  //@ assignable y, A.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy; \n"
                +"  public void m1bad(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m1good(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void m2good(int i) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ assignable y, A.xx, a.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy; //@ requires a != null; \n"
                +"  public void m3bad(int i) {\n"
                +"    ms();\n"
                +"  }\n"  // Line 20

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +"  //@ assignable xx; \n"  // Line 40
                +"  public void ms() {\n"
                +"  }\n"

                +" public TestJava() { a = new A(); }\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  x",6
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assignable) in method m3bad:  xx",7
                ,"/tt/TestJava.java:17: warning: Associated declaration",7
                
                );
    }

    @Test 
    public void testAssignableM2() {
//        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { public int x,y; public static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"

                +"  //@ assignable xx; \n"
                +"  public void m3good(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable TestJava.xx; \n"
                +"  public void m3agood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable tt.TestJava.xx; \n"
                +"  public void m3bgood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable this.xx; \n"
                +"  public void m3cgood(int i) {\n"
                +"    ms();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +"  //@ assignable xx; \n"  // Line 40
                +"  public void ms() {\n"
                +"  }\n"


                +" public TestJava() { a = new A(); }\n"
                +"}"
                
                );
    }

    @Test 
    public void testAssignableM3() {
//        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { public int x,y; public static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +"  //@ assignable xx; \n"  // Line 40
                +"  public void ms() {\n"
                +"  }\n"

                +"  //@ assignable this.x; \n"
                +"  public void mt() {\n"
                +"  }\n"

                +"  //@ assignable TestJava.xx; \n"
                +"  public void mts() {\n"
                +"  }\n"

                +" public TestJava() { a = new A(); }\n"
                +"}"
                
                );
    }

    @Test 
    public void testAssignableM4() {
//        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { public int x,y; public static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"

                +"  //@ assignable tt.TestJava.xx; \n"
                +"  public void mtts() {\n"
                +"  }\n"

                +"  //@ assignable A.xx; \n"
                +"  public void mas() {\n"
                +"  }\n"

                +"  //@ requires b == this; assignable x; \n"
                +"  public void m1z1(TestJava b) {\n"
                +"    b.m();\n"
                +"  }\n"

                +"  //@ requires b != null; assignable x; \n" // b.x is assigned but only this.x is allowed
                +"  public void m1z1bad(TestJava b) {\n"
                +"    b.m();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +" public TestJava() { a = new A(); }\n"
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assignable) in method m1z1bad:  x",8
                ,"/tt/TestJava.java:15: warning: Associated declaration",7
                );
    }

    @Test 
    public void testAssignableM5() {
//        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { public int x,y; public static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"


                +"  //@ requires b != null; assignable b.x; \n"
                +"  public void m1z2(TestJava b) {\n"
                +"    b.m();\n"
                +"  }\n"

                +"  //@ requires b == this; assignable b.x; \n"
                +"  public void m1z3(TestJava b) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ requires b == this; assignable b.x; \n"
                +"  public void m1z4(TestJava b) {\n"
                +"    this.m();\n"
                +"  }\n"

                +"  //@ requires b != null; assignable b.x; \n"
                +"  public void m1z4bad(TestJava b) {\n"
                +"    this.m();\n"
                +"  }\n"

                +"  //@ assignable x; \n"
                +"  public void m() {\n"
                +"  }\n"

                +" public TestJava() { a = new A(); }\n"
                +"}"
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assignable) in method m1z4bad:  x",11
                ,"/tt/TestJava.java:17: warning: Associated declaration",7
                
                );
    }

    @Test 
    public void testAssignableM1bug() {
        //Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public class A { int x,y; static int xx,yy; }\n"
                +"  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a; \n"

                +"  //@ requires a == this; assignable x; \n"
                +"  public void m1z1(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable x; \n"  // ERROR - a.m() assigns a.x, but only this.x is allowed
                +"  public void m1z1bad(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable a.x; \n"
                +"  public void m1z2(TestJava a) {\n"
                +"    a.m();\n"
                +"  }\n"

                +"  //@ requires a == this; assignable a.x; \n"
                +"  public void m1z3(TestJava a) {\n"
                +"    m();\n"
                +"  }\n"

                +"  //@ requires a == this; assignable a.x; \n"
                +"  public void m1z4(TestJava a) {\n"
                +"    this.m();\n"
                +"  }\n"

                +"  //@ requires a != null; assignable a.x; \n"  // this.x is assigned but only a.x is allowed
                +"  public void m1z4bad(TestJava a) {\n"
                +"    this.m();\n"  // Line 27
                +"  }\n"

                +"  //@ assignable x; \n"  // Line 29
                +"  public void m() {\n"
                +"  }\n"

                +" public TestJava() { a = new A(); }\n"
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assignable) in method m1z1bad:  x",8
                ,"/tt/TestJava.java:9: warning: Associated declaration",7
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assignable) in method m1z4bad:  x",11
                ,"/tt/TestJava.java:25: warning: Associated declaration",7
                
                );
    }


}
