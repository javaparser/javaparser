package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escaccessible extends EscBase {

    public escaccessible(String options, String solver) {
        super(options,solver);
    }
    
    @Before @Override
    public void setUp() throws Exception {
    	super.setUp();
        main.addOptions("-checkAccessible","-no-jmltesting");
    }
    
    @Test
    public void testBasic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test
    public void testConstructor() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public TestJava() {}\n"
                +"}"
                );
    }

    @Test
    public void testConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  public TestJava() { i = 1; }\n"
                +"  public int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  i",20
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleReturn2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { int i = 0; return i; }\n" // OK
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return i; }\n" // OK
                +"  int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible this.i;\n"
                +"  int m() { return i; }\n" // OK
                +"  static int i;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleReturn5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible j;\n"
                +"  int m() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  i",20
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleFA() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a; TestJava() { a = new TestJava(); } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleFA2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,a.j;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a; TestJava() { a = new TestJava(); } \n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  a.i",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleFA3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b == a;\n"
                +"  //@ accessible b.i,a;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a, b; TestJava() { a = b = new TestJava(); } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleFA4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible a,b.i;\n"
                +"  int m() { return a.i; }\n"
                +"  int i,j;\n"
                +"  TestJava a, b; TestJava() { a = b = new TestJava(); } \n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  a.i",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleAA1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i,a[*];\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleAA2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible \\everything;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                );
    }

    @Test
    public void testAccessibleAA3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires a != null && 0 <= i && i < a.length;\n"
                +"  //@ accessible a,i;\n"
                +"  int m() { return a[i]; }\n"
                +"  int i,j;\n"
                +"  int[] a; int[] b; TestJava() { a = b = new int[1]; } \n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:4: ) in method m:  a[i]",21
                ,"/tt/TestJava.java:4: warning: Associated declaration: /tt/TestJava.java:5: ",7
                );
    }

    @Test
    public void testAccessibleCall1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible i;\n"
                +"  int n() { return i; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleCall2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"  // Should FAIL
                +"  \n"
                +"  int n() { return i; }\n"  // Default accessible is \everything
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  \\everything",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleCall3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\nothing;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleCall4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i;\n"
                +"  int m() { return n(); }\n"
                +"  //@ accessible \\everything;\n"
                +"  int n() { return 0; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  \\everything",21
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleThisType() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  boolean m() { return this instanceof TestJava; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:3: ) in method m:  this",24
                ,"/tt/TestJava.java:3: warning: Associated declaration: /tt/TestJava.java:4: ",7
                );
    }

    @Test
    public void testAccessibleConditional() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ accessible i;\n"
                +"  //@ also requires !b;\n"
                +"  //@ accessible j;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleConditional2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible i,j;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleConditional3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ accessible i;\n"
                +"  //@ also requires !b;\n"
                +"  //@ accessible i;\n"
                +"  int m(boolean b) { return b ? i : j; }\n"
                +"  int i,j;\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Accessible: /tt/TestJava.java:6: ) in method m:  j",37
                ,"/tt/TestJava.java:6: warning: Associated declaration: /tt/TestJava.java:7: ",7
                );
    }



}
