package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escm extends EscBase {
    
    public escm(String options, String solver) {
        super(options,solver);
    }
    

    @Override
    public void setUp() throws Exception {
        super.setUp();
        main.addOptions("-code-math=bigint");  // To avoid overflow reports and semantics
    }
    
    /** This test checks that nested, local and anonymous classes are handled */
    @Test
    public void testNestedClass() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(TestJava o) {\n"
                +"       class C { void m() { /*@ assert false; */ }};\n"
                +"       C x;\n"
                +"       C y = new C() { void m() {/*@ assert false; */}};\n"
                +"       //@ assert false;\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"     public void m2() {\n"
                +"       //@ assert false;\n"
                +"     }\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",33
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",38
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m1",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m2",12
                );
    }
   
    /** This test checks that the specs of methods in nested, local and anonymous classes are used */
    @Test
    public void testNestedMethodSpecs() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void me(TestJava o) {\n"
                +"       class C { /*@ ensures false; */ void mc() {  }};\n"
                +"       C x;\n"
                +"       class D { void md() {  }};\n" // Line 10
                +"       D y = new D() { /*@ also ensures false; */ void md() {}};\n"
                +"       class E { /*@ ensures false; */void me() {  }};\n"
                +"       E z = new E() {  void me() {}};\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"       //@ ensures false;\n"
                +"     public void m2() {\n"
                +"     }\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method mc",45
                ,"/tt/TestJava.java:8: warning: Associated declaration",22
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method md",56
                ,"/tt/TestJava.java:11: warning: Associated declaration",33
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method me",44
                ,"/tt/TestJava.java:12: warning: Associated declaration",22
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Postcondition) in method me",30
                ,"/tt/TestJava.java:12: warning: Associated declaration",22
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2",18
                ,"/tt/TestJava.java:16: warning: Associated declaration",12
                );
    }
   
    /** This test checks that the specs of nested, local and anonymous classes are used */
    @Test
    public void testNestedClassSpecs() {
        main.addOptions("-checkFeasibility=precondition,exit");
        //main.addOptions("-progress");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(TestJava o) {\n"
                +"       class C {  \n"
                +"           //@ public invariant false;\n" 
                +"           void m() {  }};\n"  // Line 10
                +"       C x;\n"
                +"       class D { void m() {  }};\n"
                +"       D y = new D() { /*@ public invariant false;*/ void m() {}};\n"
                +"       class E { /*@ public invariant false;*/void mm() {  }};\n"
                +"       E z = new E() {  void mm() {}};\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"     //@ public invariant false;\n"
                +"     public void m2() {\n"
                +"     }\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (InvariantExit) in method C",8  // C.<init>
                ,"/tt/TestJava.java:9: warning: Associated declaration",23
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method C.m()",17  // The false invariant is triggered as a constructor postcondition
                ,"/tt/TestJava.java:13: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.1.m()",59 // m() of anonymous D
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (InvariantExit) in method E",8  // E.<init>
                ,"/tt/TestJava.java:14: warning: Associated declaration",29
                ,"/tt/TestJava.java:14: warning: Invariants+Preconditions appear to be contradictory in method E.mm()",52 
                ,"/tt/TestJava.java:15: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.2.mm()",30
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point at program exit in method tt.TestJava.m1(tt.TestJava)",15
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (InvariantExit) in method A",17  // A
                ,"/tt/TestJava.java:18: warning: Associated declaration",17
                ,"/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.A.m2()",18
                );
    }
    
    /** This tests that the specs of model classes and methods are checked */
    @Test
    public void testModelSpecs() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"

                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"

                +"  public int m1(TestJava o) {\n"
                +"       /*@ model class C {  \n"  // Invariant is false on exit
                +"           invariant false;\n" 
                +"           void mc() {  }};*/ \n"  // Line 10  // Invariants are not satisfiable on entry
                +"       /*@ model class D {  \n"
                +"           ensures false;\n" 
                +"           void md() {  }};*/ \n"   // Postcondition is false on exit
                +"       /*@ model class E {  \n"
                +"           void me() {  assert false; }};*/ \n" // Assertion is false
                +"       //@ ghost E e;\n"
                +"       return 0;\n"
                +"  }\n"

                +"  /*@ ensures false;\n"
                +"      model void mm() {}*/\n"  // Line 20  // Postcondition is false

                +"  /*@ model void mn() {  assert false;  }*/\n"  // Assertion is false

                +"  /*@ model public static class A {\n"  // Invariant is false on exit
                +"     invariant false;\n"
                +"     public void m2() {\n"  // Invariant is not satisfiable on entrance
                +"     }*/\n"
                +"  }"
                +"  public TestJava() { t = new TestJava(); }\n"
                +"}"
                +"  /*@ model class B {\n" // Invariant is false on exit
                +"     public invariant false;\n"
                +"     public void mb() {\n"  // Invariant is not satisfiable on entrance
                +"     }*/\n"
                +"  }\n"

                +"  /*@ model class BB {\n"
                +"     ensures false;\n"
                +"     public void mbb() {\n" // Postcondition is false
                +"     }*/\n"
                +"  }\n"


                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (InvariantExit) in method C",18
                ,"/tt/TestJava.java:9: warning: Associated declaration",12
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method C.mc()",17
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Postcondition) in method md",17
                ,"/tt/TestJava.java:12: warning: Associated declaration",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method me",25
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (Postcondition) in method mm",18
                ,"/tt/TestJava.java:19: warning: Associated declaration",7
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method mn",26
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (InvariantExit) in method A", 27
                ,"/tt/TestJava.java:23: warning: Associated declaration", 6
                ,"/tt/TestJava.java:24: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.A.m2()", 18
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (InvariantExit) in method B",14
                ,"/tt/TestJava.java:28: warning: Associated declaration",13
                ,"/tt/TestJava.java:29: warning: Invariants+Preconditions appear to be contradictory in method tt.B.mb()",18
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (Postcondition) in method mbb",18
                ,"/tt/TestJava.java:33: warning: Associated declaration",6
        );
    }
    
    @Test
    public void testAnon() {
        helpTCX("tt.TestJava","package tt; \n"
                                +" import org.jmlspecs.annotation.*; \n"
                                +"@NonNullByDefault public class TestJava { public int x; \n"

                                +"  public void mm() {\n"
                                +"       //@ assert new TestJava() {  public invariant x >= 0; public void mm() { } } != null; \n"  // Line 5
                                +"  }\n"
                                +"}\n"
                                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExit) in method mm",74
                                ,"/tt/TestJava.java:5: warning: Associated declaration",44

                                );
    }

    @Test
    public void testAnonX() {
        main.addOptions("-checkFeasibility=exit");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       //@ assert new TestJava() {  invariant false; int i; } != null; \n"  // Line 5 
                +"       return 0;\n"
                +"  }\n"
                
                +"  public int m2(TestJava o) {\n"
                +"       //@ assert new TestJava() {  int i; } == null; \n"  // Line 9
                +"       return 0;\n"
                +"  }\n"

                +"  public int m3(TestJava o) {\n"
                +"       //@ assert new TestJava() {  invariant true; int i; } == null; \n"  // Line 5
                +"       return 0;\n"
                +"  }\n"

                +"}\n"
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point at program exit in method tt.TestJava.m1(tt.TestJava)",14
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2",12
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m3",12
        );
    }


    @Test
    public void testAnonZ() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       boolean b = new TestJava() {  /*@ invariant false; */ int i; } != null; \n"  // Line 5 // TODO: Perhaps have the column npoint to the invariant
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"
                
                +"  public int m2(TestJava o) {\n"
                +"       boolean b = new TestJava() {  int i; } == null; \n"  // Line 9
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"

                +"  public int m3(TestJava o) {\n"
                +"       boolean b = new TestJava() {  /*@ invariant true; */ int i; } == null; \n"  // Line 5
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"

                +"}\n"
                ,"/tt/TestJava.java:6: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.m1(tt.TestJava)",12
                ,"/tt/TestJava.java:4: warning: There is no feasible path to program point at program exit in method tt.TestJava.m1(tt.TestJava)",14
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m2",12
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Assert) in method m3",12
        );
    }


    @Test
    public void testAnonY() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       //@ assert new TestJava() {  } != null; \n"  // Line 5 
                +"       return 0;\n"
                +"  }\n"
                
                +"  /*@ requires i > 0; */public TestJava() {}"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m1",19
                ,"/tt/TestJava.java:5: warning: Associated declaration",34
                ,"/tt/TestJava.java:8: warning: Precondition conjunct is false: i > 0",18
        );
    }


    @Test
    public void testMethodsInSpecs() {
        helpTCX("tt.TestJava","package tt; "
                +" import org.jmlspecs.annotation.*; \n"
                +" //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 3; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 2; \n"
                    +"  public int m1bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires m(j) == 3; \n"
                    +"  //@ ensures \\result == 3; \n"
                    +"  public int m3b(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"  // Line 22

                    +"  public void m2(int j) {\n"
                    +"       j = j+1;\n"
                    +"       //@ assert m(j) == \\old(j) + 2;\n"
                    +"  }\n"
                    
                    +"  //@ public normal_behavior\n"
                    +"  //@   requires b;\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == mm(j); \n" // Postcondition error - undefined precondition for mm
                    +"  public int m4bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires b; \n"
                    +"  //@ ensures \\result == mm(j); \n"
                    +"  public int m4(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures b ==> \\result == mm(j); \n"
                    +"  public int m4a(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"}\n"
                    ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",8
                    ,"/tt/TestJava.java:14: warning: Associated declaration",7
                    ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m4bad",28
                    ,"/tt/TestJava.java:31: warning: Associated declaration",14
                    ,"/tt/TestJava.java:36: warning: Associated method exit",8
                    ,optional("/tt/TestJava.java:28: warning: Precondition conjunct is false: b",18)
                );
    }

    @Test
    public void testFunctionsInSpecs() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public static int m(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 3; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 2; \n"
                    +"  public int m1bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires m(j) == 3; \n"
                    +"  //@ ensures \\result == 3; \n"
                    +"  public int m3b(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"  // Line 22

                    +"  public void m2(int j) {\n"
                    +"       j = j+1;\n"
                    +"       //@ assert m(j) == \\old(j) + 2;\n"
                    +"  }\n"
                    
                    +"  //@ public normal_behavior\n"
                    +"  //@   requires b;\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public static int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n" // Line 33

                    +"  //@ ensures \\result == mm(j); \n" // Postcondition error - undefined precondition for mm
                    +"  public int m4bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires b; \n"
                    +"  //@ ensures \\result == mm(j); \n"
                    +"  public int m4(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures b ==> \\result == mm(j); \n"
                    +"  public int m4a(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                    ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",8
                    ,"/tt/TestJava.java:14: warning: Associated declaration",7
                    ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m4bad",28
                    ,"/tt/TestJava.java:31: warning: Associated declaration",21
                    ,"/tt/TestJava.java:36: warning: Associated method exit",8
                    ,optional("/tt/TestJava.java:28: warning: Precondition conjunct is false: b",18)
                );
    }

    @Test
    public void testMethodsInSpecs2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                );
    }

    @Test
    public void testMethodsInSpecs3() {
        helpTCX("tt.TestJava","package tt;\n"
                +" import org.jmlspecs.annotation.*; \n"
                +" //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  //@ model public int mm(int k);\n"


                    +"}\n"
                );
    }

    @Test
    public void testMethodsInSpecs3MQ() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  //@ model public int mm(int k);\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                );
    }

        // TODO
        // Need to check anonymous classes within specs
        // Need to check non-static inner classes 
        // Need to check anonymous classes for non-static classes
   

}