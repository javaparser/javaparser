package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

/** This class of JUnit tests checks that nowarn works for esc tests.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnowarn extends EscBase {

    public escnowarn(String options, String solver) {
        super(options,solver);
    }
    
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this wasy
        //JmlEsc.escdebug = true;
    }
    
    @Test
    public void testNowarnRequires() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { public boolean b; \n"
                +"  //@   requires b;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm(); \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Precondition) in method m",7
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: b",18
                );
    }
    
    @Test
    public void testNowarnRequiresNW() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { public boolean b;  \n"
                +"  //@   requires b;\n"  
                +"  public void mm() {}\n"
                
                +"  public void m() {\n"
                +"    mm();  //@ nowarn Precondition; \n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testNowarnEnsures() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   ensures false;\n"
                +"  public void mm() {}   \n"
                
                +"  public void m() {\n" 
                +"      mm(); \n "
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method mm",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testNowarnEnsuresNW() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@   ensures false;\n"
                +"  public void mm() {}   //@ nowarn Postcondition; \n"
                
                +"  public void m() {\n" 
                +"      mm(); \n"
                +"  }\n"
                +"}"
                );
    }

    //  FIXME - disabled tests
    @Test
    public void testLocationEnsures2() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   ensures false;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    return;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                );
    }
    
    @Test
    public void testLocationSignals() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@   signals (Exception) false;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m() {\n"
                +"    throw new RuntimeException();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",9
                );
    }
    
    @Test 
    public void testLocationInvariant() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ public static invariant i>=0;\n"
                +"  //@ assignable i;\n"
                +"  public void m();\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                
                +"  public void m() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExit) in method m",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",21
                );
    }
    
    @Test
    public void testLocationInitially() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                +"  //@ public initially i>=0;\n"
                
                +"  //@ assignable i;\n"
                +"  public TestJava() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                
                +"}"
                // Change (improvement) in output for Java8
                //,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Initially) in method TestJava",21
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Initially) in method TestJava",13
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                );
    }
    
    @Test
    public void testLocationInitiallyNW1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                +"  //@ public initially i>=0;\n"
                
                +"  //@ assignable i;\n"
                +"  public TestJava() { //@ nowarn Initially;\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testLocationInitiallyNW2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                +"  //@ public initially i>=0;  nowarn Initially;\n"
                
                +"  //@ assignable i;\n"
                +"  public TestJava() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                );
    }
    
    
    @Test
    public void testLocationConstraint() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ public constraint i>=\\old(i);\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                
                +"  public void m() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m",13
                ,"/$A/tt/TestJava.jml:2: warning: Associated declaration",14
                );
    }
    
    
    @Test
    public void testLocationConstraintNW1() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ public constraint i>=\\old(i);\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                
                +"  public void m() {//@ nowarn Constraint;\n"
                +"    i = -1; return; \n" 
                +"  }\n"
                +"}"
                );
    }
    
    @Test
    public void testLocationConstraintNW2() {
        addMockFile("$A/tt/TestJava.jml","package tt; public class TestJava {\n"
                +"  //@ public constraint i>=\\old(i);  //@ nowarn Constraint;\n"
                +"}"
                );
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int i;\n"
                
                +"  public void m() {\n"
                +"    i = -1; return; \n"
                +"  }\n"
                +"}"
                );
    }
    
    // TODO: represents, non_null field, non_null parameter, non_null method
    // TODO: non_null local, any local
    // TODO: signals_only, diverges, assignable
    // TODO: called preconditions
    // TODO: called undefined: div by 0, array index neg, array index too big
    // TODO: code undefined
}
    
