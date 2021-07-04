package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

// Tests the rules about which visibility of identifiers can be used in specification constructs

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escvisibility1 extends EscBase {

    public escvisibility1(String options, String solver) {
        super(options, solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        main.addOptions("-classpath",   testspecpath);
        main.addOptions("-sourcepath",   testspecpath);
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-quiet");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
        main.addOptions("-jmltesting");
    }

   
    @Test
    public void testInvariant() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public int pb;\n"
                +"  protected int pt;\n"
                +"   int pa;\n"
                +"  private int pv;\n"
                
                +"  //@ invariant 0 == pb;\n"  // Line 7
                +"  //@ invariant 0 == pt;\n"
                +"  //@ invariant 0 == pa;\n"
                +"  //@ invariant 0 == pv;\n"
                
                +"  //@ public invariant 0 == pb;\n"
                +"  //@ public invariant 0 == pt;\n"
                +"  //@ public invariant 0 == pa;\n"
                +"  //@ public invariant 0 == pv;\n"
                
                +"  //@ protected invariant 0 == pb;\n"  // Line 15
                +"  //@ protected invariant 0 == pt;\n"
                +"  //@ protected invariant 0 == pa;\n"
                +"  //@ protected invariant 0 == pv;\n"
                
                +"  //@ private invariant 0 == pb;\n"
                +"  //@ private invariant 0 == pt;\n"
                +"  //@ private invariant 0 == pa;\n"
                +"  //@ private invariant 0 == pv;\n"
                +"}"
                ,"/tt/TestJava.java:7: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:15: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:17: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:19: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:21: An identifier with package visibility may not be used in a invariant clause with private visibility",30
                );
    }
    
    @Test
    public void testInvariantM() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  /*@ pure */public int pb(){return 0; };\n"
                +"  /*@ pure */protected int pt(){return 0; };\n"
                +"  /*@ pure */ int pa(){return 0; };\n"
                +"  /*@ pure */private int pv(){return 0; };\n"
                
                +"  //@ invariant 0 == pb();\n"  // Line 7
                +"  //@ invariant 0 == pt();\n"
                +"  //@ invariant 0 == pa();\n"
                +"  //@ invariant 0 == pv();\n"
                
                +"  //@ public invariant 0 == pb();\n"
                +"  //@ public invariant 0 == pt();\n"
                +"  //@ public invariant 0 == pa();\n"
                +"  //@ public invariant 0 == pv();\n"
                
                +"  //@ protected invariant 0 == pb();\n"  // Line 15
                +"  //@ protected invariant 0 == pt();\n"
                +"  //@ protected invariant 0 == pa();\n"
                +"  //@ protected invariant 0 == pv();\n"
                
                +"  //@ private invariant 0 == pb();\n"
                +"  //@ private invariant 0 == pt();\n"
                +"  //@ private invariant 0 == pa();\n"
                +"  //@ private invariant 0 == pv();\n"
                +"}"
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:17: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                );
    }
    
    @Test
    public void testInvariant2() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  /*@ spec_public */ protected int pt;\n"
                +"  /*@ spec_public */  int pa;\n"
                +"  /*@ spec_public */ private int pv;\n"
                
                +"  //@ invariant 0 == pt;\n"  // Line 6
                +"  //@ invariant 0 == pa;\n"
                +"  //@ invariant 0 == pv;\n"
                
                +"  //@ public invariant 0 == pt;\n"
                +"  //@ public invariant 0 == pa;\n"
                +"  //@ public invariant 0 == pv;\n"
                
                +"  //@ protected invariant 0 == pt;\n"
                +"  //@ protected invariant 0 == pa;\n"
                +"  //@ protected invariant 0 == pv;\n"
                
                +"  //@ private invariant 0 == pt;\n"
                +"  //@ private invariant 0 == pa;\n"
                +"  //@ private invariant 0 == pv;\n"

                +"  /*@ spec_protected */  int pat;\n"
                +"  /*@ spec_protected */ private int pvt;\n"
                
                +"  //@ invariant 0 == pat;\n"
                +"  //@ invariant 0 == pvt;\n"
                
                +"  //@ public invariant 0 == pat;\n"
                +"  //@ public invariant 0 == pvt;\n"
                
                +"  //@ protected invariant 0 == pat;\n"
                +"  //@ protected invariant 0 == pvt;\n"
                
                +"  //@ private invariant 0 == pat;\n"
                +"  //@ private invariant 0 == pvt;\n"
                +"}"
                ,"/tt/TestJava.java:6: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:7: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:13: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:14: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:15: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:16: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:17: An identifier with public visibility may not be used in a invariant clause with private visibility",30
 
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:21: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:22: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:23: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:26: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:27: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                );
    }
    
    @Test
    public void testInClause() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  //@ model public int pb;\n"
                +"  //@ model protected int pt;\n"
                +"  //@ model  int pa;\n"
                +"  //@ model private int pv;\n"
                
                +"  public int x1; //@ in pb;\n"  // Line 7
                +"  public int x2; //@ in pt;\n"
                +"  public int x3; //@ in pa;\n"
                +"  public int x4; //@ in pv;\n"
                
                +"  protected int y1; //@ in pb;\n"
                +"  protected int y2; //@ in pt;\n"
                +"  protected int y3; //@ in pa;\n"
                +"  protected int y4; //@ in pv;\n"
                
                +"   int z1; //@ in pb;\n"
                +"   int z2; //@ in pt;\n"
                +"   int z3; //@ in pa;\n"
                +"   int z4; //@ in pv;\n"
                
                +"  private int t1; //@ in pb;\n"
                +"  private int t2; //@ in pt;\n"
                +"  private int t3; //@ in pa;\n"
                +"  private int t4; //@ in pv;\n"
                
                +"}"
                ,"/tt/TestJava.java:8: An identifier with protected visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:9: An identifier with package visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:10: An identifier with private visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:13: An identifier with package visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a in clause with package visibility",19
                );
    }
    
    @Test
    public void testRequires1() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  public void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:12: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:12: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires2() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  protected void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires3() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"   void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    
    @Test
    public void testRequires4() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"class B { \n"
                
                +"  public boolean pb;\n"
                +"  protected boolean pt;\n"
                +"   boolean pa;\n"
                +"  private boolean pv;\n"
                
                +"  /*@ spec_public */ protected boolean ptb;\n"
                +"  /*@ spec_public */  boolean pab;\n"
                +"  /*@ spec_public */ private boolean pvb;\n"
                
                +"  /*@ spec_protected */  boolean pat;\n"
                +"  /*@ spec_protected */ private boolean pvt;\n"
                
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also private normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also protected normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  //@ also public normal_behavior\n"
                +"  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;\n"
                +"  private void m(){}\n"
                +"}"
                ,"/tt/TestJava.java:12: warning: There is no point to a specification case having more visibility than its method",7
                ,"/tt/TestJava.java:14: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }
    

    @Test
    public void testThisStarDefault() {
        helpTCX("tt.A","package tt; public class A {\n" +
                "int i; \n" +
                "public A() { i = 0; } \n}"
//                ,"/tt/A.java:3: warning: The prover cannot establish an assertion (Assignable) in method A:  i",16
//                ,"/tt/A.java:3: warning: Associated declaration",8
                );
    }

    @Test
    public void testThisStarDefault1() {
        helpTCX("tt.A","package tt; public class A {\n" +
                "int i; \n" +
                "//@ requires true;\n" +
                "public A() { i = 0; } \n}"
//                ,"/tt/A.java:4: warning: The prover cannot establish an assertion (Assignable) in method A:  i",16
//                ,"/tt/A.java:3: warning: Associated declaration",5
                );
    }

    @Test
    public void testThisStar0() {
        helpTCX("tt.A","package tt; public class A {\n" +
                "int i; \n" +
                "//@ pure\n" +
                "public A() { i = 0; } \n}"
//                ,"/tt/A.java:4: warning: The prover cannot establish an assertion (Assignable) in method A:  i",16
//                ,"/tt/A.java:3: warning: Associated declaration",5
                );
    }

    @Test
    public void testThisStar1() {
        helpTCX("tt.A","package tt; public class A {\n public int i; \n" +
                "//@ pure\n" +
                "public A() { i = 0; } \n}"
                );
    }

    @Test
    public void testThisStar2() {
        helpTCX("tt.A","package tt; public class A {\n private int i; \n" +
                "//@ pure\n" +
                "public A() { i = 0; } \n}"
//                ,"/tt/A.java:4: warning: The prover cannot establish an assertion (Assignable) in method A:  i",16
//                ,"/tt/A.java:3: warning: Associated declaration",5
                );
    }

    @Test
    public void testThisStar3() {
        helpTCX("tt.A","package tt; public class A {\n protected int i; \n" +
                "//@ pure\n" +
                "public A() { i = 0; } \n}"
//                ,"/tt/A.java:4: warning: The prover cannot establish an assertion (Assignable) in method A:  i",16
//                ,"/tt/A.java:3: warning: Associated declaration",5
                );
    }

    @Test
    public void testThisStar4() {
        helpTCX("tt.A","package tt; public class A {\n public int i; \n" +
                "//@ pure\n" +
                "private A() { i = 0; } \n}"
                );
    }

    @Test
    public void testThisStar5() {
        helpTCX("tt.A","package tt; public class A {\n private int i; \n" +
                "//@ pure\n" +
                "private A() { i = 0; } \n}"
                );
    }

    @Test
    public void testThisStar6() {
        helpTCX("tt.A","package tt; public class A {\n protected int i; \n" +
                "//@ pure\n" +
                "private A() { i = 0; } \n}"
                );
    }

    @Test
    public void testThisStar7() {
        helpTCX("tt.A","package tt; public class A {\n  int i; \n" +
                "//@ pure\n" +
                "private A() { i = 0; } \n}"
                );
    }

    @Test
    public void testThisStar8() {
        helpTCX2("tx.B","package tx; public class B {\n protected int i;\n}",
                "tt.A","package tt; public class A extends tx.B {\n \n" +
                "//@ pure\n" +
                " A() { i = 0; } \n}"
//                ,"/tt/A.java:4: warning: The prover cannot establish an assertion (Assignable) in method A:  i",10
//                ,"/tt/A.java:3: warning: Associated declaration",5
                );
    }

    @Test
    public void testThisStar9() {
        helpTCX2("tx.B","package tx; public class B {\n protected int i;\n}",
                "tt.A","package tt; public class A extends tx.B {\n \n" +
                "//@ pure\n" +
                "protected A() { i = 0; } \n}"
                );
    }
    
    // Testing nested classes

    // FIXME - why the duplicate errors
    @Test
    public void testNestedPrivate() {
        expectedExit = 1;
        helpTCX2("tt.B","package tt; public class B {\n static tt.A.P pp = A.Q.q; }\n", // No tt.A.P, No A.Q.q
                "tt.A","package tt; public class A  {\n \n" +
                       "static private class P { static private int p; }\n" +
                       "static private class Q { static public int q = A.P.p ; }}\n" +  // OK
                       "class AA { static int x = A.P.p + A.Q.q; }\n" //No tt.A.P, tt.A.Q
                ,"/tt/B.java:2: tt.A.P has private access in tt.A",13
                ,"/tt/B.java:2: tt.A.P has private access in tt.A",13
                ,"/tt/B.java:2: tt.A.Q has private access in tt.A",22
                ,"/tt/B.java:2: tt.A.Q has private access in tt.A",22
                ,"/tt/A.java:5: tt.A.P has private access in tt.A",28
                ,"/tt/A.java:5: tt.A.P has private access in tt.A",28
                ,"/tt/A.java:5: tt.A.Q has private access in tt.A",36
                ,"/tt/A.java:5: tt.A.Q has private access in tt.A",36
                );
    }
    
    @Test
    public void testNestedProtected() {
        expectedExit = 1;
        helpTCX2("tt.B","package tx; public class B {\n static tt.A.P pp = tt.A.Q.q; }\n", // No tt.A.P, No A.Q.q
                "tt.A","package tt; public class A  {\n \n" +
                       "static protected class P { static private int p; }\n" +
                       "static protected class Q { static public int q = A.P.p ; }}\n" +  // OK
                       "class AA { static int x = A.P.p + A.Q.q; }\n" // q OK - same package
                ,"/tt/B.java:2: tt.A.P has protected access in tt.A",13
                ,"/tt/B.java:2: tt.A.P has protected access in tt.A",13
                ,"/tt/B.java:2: tt.A.Q has protected access in tt.A",25
                ,"/tt/B.java:2: tt.A.Q has protected access in tt.A",25
                ,"/tt/A.java:5: p has private access in tt.A.P",30
                );
    }
    

}
