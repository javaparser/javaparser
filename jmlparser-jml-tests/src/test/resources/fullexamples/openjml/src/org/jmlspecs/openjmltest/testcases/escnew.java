package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnew extends EscBase {

    public escnew(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    @Test
    public void testPrecondition1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  public void m2bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m1good(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m2good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ also\n"
                +"  //@ requires i==0;\n"
                +"  public void m3good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }

    @Test
    public void testPrecondition1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  public void m2bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m1good(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m2good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ also\n"
                +"  //@ requires i==0;\n"
                +"  public void m3good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }
    

    @Test
    public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i>0;\n"
                +"  //@ ensures false;\n"
                +"  public void m1a(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ requires i<0;\n"
                +"  //@ ensures false;\n"
                +"  public void m1b(int i) {\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m1a",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m1b(int)",15
                );
    }
    
    @Test
    public void testPrecondition3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i >= 0 && a[i]>0;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i < a.length && a[i]>0;\n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ requires a[i]>0;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1bad",27
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2bad",33
                );
    }

    @Test
    public void testPrecondition3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 10 && i < 5 && a[i]>0 ;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ requires a[i]>0;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",43
                );
    }


    @Test
    public void testPostcondition1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception) false;\n"
                +"  public void m1bad(int[] a, int i) throws RuntimeException {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m3bad(int[] a, int i) {\n"
                +"     return;\n"
                +"  }\n"
                
                +"  //@ ensures true;\n"
                +"  //@ signals (Exception e)  false;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ ensures false;\n"
                +"  public void m2good(int[] a, int i) throws RuntimeException {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",15
                ,"/tt/TestJava.java:7: warning: Associated declaration",7
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",6
                ,"/tt/TestJava.java:10: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testPostcondition2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ ensures false;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ ensures true;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"      if (i == 0) \n"
                +"         return;\n"
                +"      else\n"
                +"         return;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ ensures true;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ ensures false;\n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"      if (i == 0) \n"
                +"         return;\n"
                +"      else\n"
                +"         return;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testPostcondition3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ signals (Exception e) true;\n"
                +"  public void m1bad(int[] a, int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw new Exception();\n" // Line 10
                +"      else\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  //@ signals (Exception e) true;\n"
                +"  //@ also\n"
                +"  //@ requires i!= 0;\n"
                +"  //@ signals (Exception e) false;\n"
                +"  public void m2bad(int[] a, int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw new Exception();\n"
                +"      else\n"
                +"         throw new Exception();\n" // Line 23
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad",10
                ,"/tt/TestJava.java:18: warning: Associated declaration",7
                );
    }
    
    // Tests use of \exception token
    @Test
    public void testPostcondition4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception e) \\exception == null;\n"
                +"  public void m1bad(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ signals (Exception e) \\exception != null;\n"
                +"  public void m1good(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"  //@ signals (Exception) \\exception != null;\n"
                +"  public void m2good(int[] a, int i) throws Exception {\n"
                +"         throw new Exception();\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5() {
    	main.addOptions("-code-math=java","-spec-math=java"); // Just to avoid overflow warnings
    	helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int iii;\n"
                
                +"  //@ public normal_behavior ensures iii == \\old(iii) + 3;\n"
                +"  public void m1() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures iii == \\old(iii) + 3;\n"
                +"  public void m1bad() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                
                +"  //@ public normal_behavior assignable iii; ensures iii == \\old(iii) + 1;\n"
                +"  public void inc()  {\n"
                +"         ++iii;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:10: warning: Associated declaration",30
                );
    }
    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5a() {
    	main.addOptions("-code-math=java","-spec-math=java"); // Just to avoid overflow warnings
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int i;\n"
                
                +"  //@ public normal_behavior ensures i == \\old(i) + 3;\n"
                +"  public void m1() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures i == \\old(i) + 3;\n"
                +"  public void m1bad() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                // Default is assignable \everything
                +"  //@ public normal_behavior ensures i == \\old(i) + 1;\n"
                +"  public void inc()  {\n"
                +"         ++i;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:10: warning: Associated declaration",30
                );
    }
    
    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5x() {
    	main.addOptions("-code-math=bigint","-spec-math=bigint"); // Just to avoid overflow warnings
    	helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int iii;\n"
                
                +"  //@ public normal_behavior ensures iii == \\old(iii) + 3;\n"
                +"  public void m1() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures iii == \\old(iii) + 3;\n"
                +"  public void m1bad() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                
                +"  //@ public normal_behavior assignable iii; ensures iii == \\old(iii) + 1;\n"
                +"  public void inc()  {\n"
                +"         ++iii;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:10: warning: Associated declaration",30
                );
    }
    // Tests use of \old token in called methods
    @Test
    public void testPostcondition5ax() {
    	main.addOptions("-code-math=bigint","-spec-math=bigint"); // Just to avoid overflow warnings
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int i;\n"
                
                +"  //@ public normal_behavior ensures i == \\old(i) + 3;\n"
                +"  public void m1() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior ensures i == \\old(i) + 3;\n"
                +"  public void m1bad() {\n"
                +"         inc();\n"
                +"         inc();\n"
                +"  }\n"
                
                // Default is assignable \everything
                +"  //@ public normal_behavior ensures i == \\old(i) + 1;\n"
                +"  public void inc()  {\n"
                +"         ++i;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                ,"/tt/TestJava.java:10: warning: Associated declaration",30
                );
    }
    
    // FIXME - add checks on object fields, quantifier variables
    // FIXME - need attribute checks on scopes of variables
    @Test
    public void testLabeled() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 0; \n"
                +"  public void m1good(int i) throws Exception {\n"
                +"       int j = 0;\n"
                +"       //@ assert j == 0;\n"
                +"       a: j = 1; i = 1;\n"
                +"       //@ assert \\old(i) == 0;\n"
                +"       b: j = 2; i = 2;\n"
                +"       //@ assert \\old(j,a) == 0;\n"
                +"       //@ assert \\old(i,a) == 0;\n"
                +"       //@ assert \\old(j,b) == 1;\n"
                +"       //@ assert \\old(i,b) == 1;\n"
                +"       //@ assert \\pre(i) == 0;\n"
                +"       \n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testBox() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == 7; \n"
                +"  public int m1good()  {\n"
                +"      Integer k = 7;\n"
                +"      int i = k;\n"
                +"      return i;\n"
                +"  }\n"
                +"  }\n"
                
                );
    }
    
    @Test
    public void testMethodInvocation() {
        main.addOptions("-logic=AUFNIRA");
        Assume.assumeTrue(runLongTests);
        Assume.assumeTrue(!"cvc4".equals(solver)); // CVC4 complains about the integer-division operation (FIXME) does not handle integer division
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  /*@ signals_only \\nothing;*/\n" // FIXME - this used to be part of the default if there were no spec cases at all.
                +"  public int z(int i)  {\n"
                +"      return i;\n"
                +"  }\n"
                
                +"  public int m1bad(int k)  {\n"
                +"      int i = z(k/k);\n"
                +"      return i;\n"
                +"  }\n"
                
                +"  public void m2bad(int k)  {\n"
                +"      z(k/k);\n"
                +"  }\n"
                
                +"  //@ requires k > 0;  \n"
                +"  public int m1good(int k)  {\n"
                +"      int i = z(k/k);\n"
                +"      return i;\n"
                +"  }\n"
                +"  }\n"
                
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",10

                );
    }

    // Almost duplicate of escnew
    @Test public void testMethodInvocation1() {
        Assume.assumeTrue(runLongTests);
        main.addOptions("-logic=AUFLIRA");
        //if ("cvc4".equals(solver)) return; // CVC4 complains about the integer-division operation (FIXME)
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int z(int i)  {\n"
                +"      return i;\n"
                +"  }}\n"
                

                );
    }
    


    @Test
    public void testSwitch() {
        main.addOptions("-code-math=math"); // To avoid warnings because of overflow
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == i* 2 + 1; \n"
                +"  public int m1bad(int i) throws Exception {\n"
                +"      int k;\n"
                +"       switch (i) {\n"
                +"        case 1: k = 3; break;\n"
                +"        default: k = i + i + 1; break;\n"
                +"        case 2: k = 6; return k;\n"
                +"       } return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i* 2 + 1; \n"
                +"  public int m1good(int i) throws Exception {\n"
                +"      int k;\n"
                +"       switch (i) {\n"
                +"        case 1: k = 3; break;\n"
                +"        default: k = i + i + 1; break;\n"
                +"        case 2: k = 5; break;\n"
                +"       } return k;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",24
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testTry() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures \\result == 1; \n"
                +"  public int m1bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; \n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        }return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == 0; \n"
                +"  public int m2bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 0; \n"
                +"  public int m3bad() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"       } finally {\n"
                +"           k = 3;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 1; \n"
                +"  public int m1good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; return k;\n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        } \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 2; \n"
                +"  public int m0good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; \n"
                +"       } finally {\n"
                +"           k = 2;\n"
                +"        } return k;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == 2; \n"   // Line 50
                +"  public int m2good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"        } return k; \n"
                +"  }\n"
                
                +"  //@ ensures \\result == 3; \n"
                +"  public int m3good() throws Exception {\n"
                +"      int k;\n"
                +"       try {\n"
                +"        k=1; throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           k = 2;\n"
                +"       } finally {\n"
                +"           k = 3\n;"
                +"        } return k; \n"
                +"  }\n"
                
                +"  static public int kk;\n"

                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  false; \n"
                +"  public int m4good(int i ) throws Exception {\n"
                +"       try {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       } catch (RuntimeException e) {\n"
                +"           kk = 2;\n"
                +"        } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
                +"  public int m5good(int i) throws Exception {\n"
                +"       try {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"        } finally {} \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
                +"  public int m6good(int i) throws Exception {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e) kk == 4; \n"
                +"  public int m7good(int i) throws Exception {\n"
                +"       try {\n"
                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
                +"           try {\n"
                +"             kk=2; if (i == 1) throw new RuntimeException();\n"
                +"           } finally { kk = 5; } \n"
                +"       } finally { kk = 4; } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures i==0 ==> \\result == 4; signals (Exception e) false; \n"
                +"  public int m8good(int i) throws Exception {\n"
                +"       try {\n"
                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       } finally { if (i == 0) return 4; } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",11
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",11
                ,"/tt/TestJava.java:21: warning: Associated declaration",7
                
                );
    }
    
    @Test // FIXME _ needs type relationships
    public void testTry2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  static public int kk;\n"
                
                +"  //@ assignable kk;\n"
                +"  //@ ensures \\result == 3; signals (Exception e)  false; \n"
                +"  public int m4agood(int i ) throws Exception {\n"
                +"       try {\n"
                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
                +"       } catch (Exception e) {\n"
                +"           kk = 2;\n"
                +"        } \n"
                +"       kk = 3;\n"
                +"       return kk; \n"
                +"  }\n"
                
                
                +"}"
                );
    }
    
    @Test
    public void testUnreachable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) {\n"
                +"      if (i == 0) { \n"
                +"         //@ unreachable;\n"
                +"      }\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) {\n"
                +"      if (i == 0) { \n"
                +"         //@ unreachable;\n"
                +"      }\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Unreachable) in method m1bad",14
                );
    }
    

    @Test
    public void testGhostSet() {
        main.addOptions(JmlOption.KEYS.optionName(), "DEBUG");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ set k = 1;\n"
                +"      //@ assert k == 0; \n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ set k = 1;\n"
                +"      //@ assert k == 1; \n"
                +"  }\n"
                
                +"  public void m2bad(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 0; \n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m2good(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 1; \n"
                +"  }\n"

                // FIXME - need to handle jml constructs in set, debug statements
//                +"  public void m3bad() {\n"
//                +"      //@ ghost boolean k = true;"
//                +"      //@ set k = (k <=!=> k);\n"
//                +"      //@ assert k; \n"
//                +"  }\n"
//                
//                +"  public void m3good() {\n"
//                +"      //@ ghost boolean k = true;"
//                +"      //@ set k = (k <==> k);\n"
//                +"      //@ assert k; \n"
//                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",11
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method m2bad",11
                );
    }
    
    @Test
    public void testGhostSetNoDebug() {
        // debug is not enabled 
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m2good(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 0; \n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m2bad(int i) {\n"
                +"      //@ ghost int k = 0;"
                +"      //@ debug k = 1;\n"
                +"      //@ assert k == 1; \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2bad",11
                );
    }
    
    @Test
    public void testHavoc() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1good() {\n"
                +"      int i = 0; \n"
                +"      //@ assert i == 0;\n"
                +"  }\n"
                
                +"  public void m1bad() {\n"
                +"      int i = 0; \n"
                +"      //@ havoc i; \n"
                +"      //@ assert i == 0;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m1bad",11
                );
    }
    
    
    // FIXME _ check that different return or throw statements are properly pointed to

    // FIXME - needs proper expansion of array accesses
    @Test
    public void testPostcondition10() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ ensures a[i]>0;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"

                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ ensures a[i]==true || a[i]==false;\n"
                +"  public void m1good(boolean[] a, int i) {\n"
                +"  }\n"

                +"}"
                ,anyorder(
                        seq("/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",16
                        	,"/tt/TestJava.java:5: warning: Associated method exit",4
                        	)
                        ,seq("/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1bad",16
                        		,"/tt/TestJava.java:5: warning: Associated method exit",4
                        		)
                        ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",15
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                                )
                );
    }

    @Test
    public void testPostcondition1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception) false;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    


    // FIXME - need tests with multiple ensures and various cases
    
    // FIXME - test definedness in postconditions
    
    // FIXME - exceptional postconditions
    
    // FIXME - need precondition checks for calling methods
    // FIXME - need checks for ensures assumptions when calling methods
    // FIXME - complete assignables
    // FIXME - assignables for method calls

    // Just testing binary and unary 
    @Test
    public void testBinaryUnary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result ==4;\n"
                +"  public int m1bad() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 3;\n"
                +"  public int m1ok() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public int m2bad(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result <= 0;\n"
                +"  public int m2ok(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                );
    }

    @Test
    public void testIncDec() {
    	main.addOptions("-code-math=java","-spec-math=java"); // Just to avoid overflow warnings
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { static public int i; \n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ ensures i == \\old(i) + 1;\n"
                +"  public int m1ok() {\n"
                +"    return ++i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ ensures i == \\old(i) - 1;\n"
                +"  public int m2ok() {\n"
                +"    return --i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == \\old(i);\n"
                +"  //@ ensures i == \\old(i) + 1;\n"
                +"  public int m3ok() {\n"
                +"    return i++;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ ensures i == \\old(i) + 1;\n"
                +"  public int m3bad() {\n"
                +"    return i++;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == \\old(i);\n"
                +"  //@ ensures i == \\old(i) - 1;\n"
                +"  public int m4ok() {\n"
                +"    return i--;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  //@ ensures \\result == i;\n"
                +"  //@ ensures i == \\old(i) - 1;\n"
                +"  public int m4bad() {\n"
                +"    return i--;\n"
                +"  }\n"
                
               
                +"}"
                ,"/tt/TestJava.java:25: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:22: warning: Associated declaration",7
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:34: warning: Associated declaration",7
                );
    }

    // Just testing binary and unary 
    @Test
    public void testJMLBinaryUnary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires p ==> q;\n"
                +"  //@ ensures !p || q;\n"
                +"  public void m1ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <==> q;\n"
                +"  //@ ensures p == q;\n"
                +"  public void m2ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <=!=> q;\n"
                +"  //@ ensures p != q;\n"
                +"  public void m3ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p <== q;\n"
                +"  //@ ensures p || !q;\n"
                +"  public void m4ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires !p || q;\n"
                +"  //@ ensures p ==> q;\n"
                +"  public void m5ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p == q;\n"
                +"  //@ ensures p <==> q;\n"
                +"  public void m6ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p != q;\n"
                +"  //@ ensures p <=!=> q;\n"
                +"  public void m7ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                +"  //@ requires p || !q;\n"
                +"  //@ ensures p <== q;\n"
                +"  public void m8ok(boolean p, boolean q) {\n"
                +"  }\n"
                
                
                +"}"
                );
    }

    @Test
    public void testConditional2() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-code-math=safe");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i < 100000;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires i < 100000;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testConditional() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-code-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires i < 100000;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m2bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"  // Error: silent overflow - result may be less than i
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                );
    }

    @Test
    public void testConditional3() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-code-math=math");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testShortCircuit() {
        Assume.assumeTrue(runLongTests);
        Assume.assumeTrue(!"cvc4".equals(solver)); // SKIPPING cvc4 does not handle integer division
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { int f; \n"
                
                // The " ? true : true" is inserted so that the solver is not required to handle non-linear arithmetic
                +"  public boolean m1bad(boolean b, int i) {\n"
                +"    return i != 0 || (20/i <= 20 ? true : true) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean b, int i) {\n"
                +"    return i == 0 || (i/i > 0 ? true : true) ;\n"
                +"  }\n"
                
                +"  public boolean m2bad(boolean b, int i) {\n"
                +"    return i == 0 && (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  public boolean m2ok(boolean b, int i) {\n"
                +"    return i != 0 && (20/i <= 20 ? true : true) ;\n"
                +"  }\n"
                
                +"  public boolean m3bad(@Nullable TestJava t) {\n"
                +"    return t != null || t.f == 1 ;\n"
                +"  }\n"
                
                +"  public boolean m3ok(@Nullable TestJava t) {\n"
                +"    return t != null && t.f == 1 ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4ok(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4bad(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == false;\n"
                +"  public boolean m5ok(boolean a, boolean b) {\n"
                +"    return a && b ;\n"
                +"  }\n"
                
                // FIXME - it should be valid, but returns unknown
                // Keep these - the result is unknown on some solvers and
                // exposed a bug in handling unknown results
                +"  //@ requires i < 2 && i > -2; ensures \\result;\n"
                +"  public boolean m1bugOK(int i) {\n"
                +"    return i == 0 || (20/i <= 20 ? true : true) ;\n"
                +"  }\n"
                
                // Look at the counterexample on this one (TODO)
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bug(int i) {\n"
                +"    return i == 0 || (20/i <= 20 ? true : true) ;\n"
                +"  }\n"
                
                +"  //@ requires i < 30 && i > -30; ensures \\result;\n"
                +"  public boolean m1bugOK2(int i) {\n"
                +"    return i == 0 || (20/i <= 20 ? true : true) ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad",26
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:31: warning: Associated declaration",7
                );
    }

    // FIXME - almost duplciate with escnew
    @Test public void testShortCircuitDup() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { int f; \n"
                
                +"  public boolean m1bad(boolean b, int i) {\n"
                +"    return i != 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean b, int i) {\n"
                +"    return i == 0 || (i/i > 0) ;\n"
                +"  }\n"
                
                +"  public boolean m2bad(boolean b, int i) {\n"
                +"    return i == 0 && (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  public boolean m2ok(boolean b, int i) {\n"
                +"    return i != 0 && (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  public boolean m3bad(@Nullable TestJava t) {\n"
                +"    return t != null || t.f == 1 ;\n"
                +"  }\n"
                
                +"  public boolean m3ok(@Nullable TestJava t) {\n"
                +"    return t != null && t.f == 1 ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4ok(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4bad(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == false;\n"
                +"  public boolean m5ok(boolean a, boolean b) {\n"
                +"    return a && b ;\n"
                +"  }\n"
                
                // FIXME - it should be valid, but returns unknown
                // Keep these - the result is unknown on some solvers and
                // exposed a bug in handling unknown results
                +"  //@ requires i < 2 && i > -2; ensures \\result;\n"
                +"  public boolean m1bugOK(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                // Look at the counterexample on this one (TODO)
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bug(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  //@ requires i < 30 && i > -30; ensures \\result;\n"
                +"  public boolean m1bugOK2(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad",26
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:31: warning: Associated declaration",7
//                ,"/tt/TestJava.java:52: warning: The prover cannot establish an assertion (Postcondition) in method m1bug",5
//                ,"/tt/TestJava.java:50: warning: Associated declaration",7
                );
    }


    @Test public void testJmlLabelExpression() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ requires true;\n"
                +"  //@ ensures b ==> (i!=5) ;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    //@ ghost boolean bb = (\\lbl LBL_BB b);\n"
                +"    //@ ghost boolean bbp = (\\lblpos LBL_BB2 (i!=5));\n"
                +"    //@ ghost boolean bbn = (\\lblneg LBL_BB3 (i!=5));\n"
                +"    //@ ghost int ii = (\\lbl LBL_BBI i);\n"
                +"    return 1;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: Label LBL_BB has value true",34
                ,"/tt/TestJava.java:8: warning: Label LBL_BB3 has value false",38
                ,"/tt/TestJava.java:9: warning: Label LBL_BBI has value 5",30
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1ok",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }


    @Test
    public void testBoolOpsParens() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bad(boolean p, boolean q) {\n"
                +"    return p == q;\n"
                +"  }\n"
                
                +"  //@ requires p && q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean p, boolean q) {\n"
                +"    return ((p == q)) ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2bad(boolean p, boolean q) {\n"
                +"    return p != q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2ok(boolean p, boolean q) {\n"
                +"    return p != q ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3bad(boolean p, boolean q) {\n"
                +"    return p == !q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3ok(boolean p, boolean q) {\n"
                +"    return p == !q ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
    }

    @Test
    public void testBoxing() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int m1bad(/*@ nullable */ Integer i) {\n"
                +"    return i;\n"
                +"  }\n"
                
                +"  public int m1ok(/*@ non_null */ Integer i) {\n"
                +"    return i;\n"
                +"  }\n"
                
                +"  public void m2ok() {\n"
                +"    int i = 3;\n"
                +"    Integer ii = i;\n"
                +"    int j = ii;\n"
                +"    //@ assert i == j;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad",5
                );
    }

    @Test  // FIXME - problem is an infinite loop with use of consistentWithEquals - invariants use it, but the invariants are part of the specs for the (model pure) consistentWithEquals method
    public void testSelect() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1bad() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires this.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1ok() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2bad() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2ok() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3bad(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public int m3bad2(/*@nullable*/ TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires p.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3ok(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  public void m4ok(TestJava p) {\n"
                +"    System.out.println(\"A\");\n"
                +"  }\n"
                
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:15: warning: Associated declaration",7
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:25: warning: Associated declaration",7
                ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad2",13
                );
    }
    @Test
    public void testChangedParam() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                +"  //@ requires i < 100;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                +"  //@ requires i < 100;\n"
                +"  //@ ensures \\result == i+1;\n"
                +"  public int m1good(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
    }

    @Test
    public void testNameReused() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1good() {\n"
                +"    { int s = 0; /*@ assert s == 0; */ }\n"
                +"    { int s = 1; /*@ assert s == 1; */ }\n"
                +"  }\n"
                
                +"  public void m1bad() {\n"
                +"    { int s = 0; /*@ assert s == 1; */ }\n"
                +"    { int s = 1; /*@ assert s == 0; */ }\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1bad",22
                );
    }

    @Test
    public void testNonNullField() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public Object nnf;\n"
                +"  public /*@ nullable*/ Object f;\n"

                // FIXME - these crash Z3
//                +"  public Object m1bad() {\n"
//                +"    return this.f ;\n"
//                +"  }\n"
//                
//                +"  public Object m1ok() {\n"
//                +"    return this.nnf ;\n"
//                +"  }\n"
                
                +"  public void m2bad() {\n"
                +"    nnf = null ;\n"
                +"  }\n"
                
//                +"  public void m2ok() {\n"
//                +"    f = null ;\n"
//                +"  }\n"

                +"  public TestJava() { nnf = new Object(); }"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",9
                );
    }

    // This tests a bug in which static invariants were not part of the VC. 
    // The problem is that helper methods do not inherit invariants, even ones that are fixed, such as those that define the values of fields
    @Test
    public void testInvariantInheritance2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                
                +"  public static int CHILD = 3;\n"
                +"  //@ static public invariant CHILD == 3;\n"

                
                +"  //@ helper pure \n"
                +"  public static void m1() {\n"
                +"    //@ assert CHILD == 3 ;\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1",9
                );
    }

    @Test
    public void testAsList() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                +"  public enum E { A}; \n"
                
                +"  public static void m1() {\n"
                +"    java.util.List<E> m = java.util.Arrays.asList(new E[]{E.A});\n"
                +"  }\n"
                +"}\n"
                );
        }
    @Test // Allow final on invariant to mean assume regardless of helper status
    public void testInvariantInheritance() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                
                +"  public final static int CHILD; static { CHILD = 3; }\n"
                +"  //@ static final public invariant CHILD == 3;\n"

                +"  //@ public normal_behavior ensures true; static_initializer\n"
                +"  //@ helper pure \n"
                +"  public static void m1() {\n"
                +"    //@ assert CHILD == 3 ;\n"
                +"  }\n"
                +"}\n"
                );
        }
    @Test
    public void testInvariantInheritance3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                
                +"  public /*@ final */ static int CHILD = 3;\n"

                
                +"  //@ helper pure \n"
                +"  public static void m1() {\n"
                +"    //@ assert CHILD == 3 ;\n"
                +"  }\n"
                +"}\n"
                );
        }
    
    @Test
    public void testInvariantInheritanceArray() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava  { \n"
                
                +"  public /*@ final */ static int[] FIELD = new int[]{1,2,3,4,5};\n"
                +"  public /*@ final */ static int[] FIELD2 = {1,2,3,4,5,6};\n"

                +"  //@ public normal_behavior ensures true; static_initializer\n"
                
                +"  //@  pure \n"
                +"  public static void m1() {\n"
                +"    //@ assert H.ZZZZ == 79 ;\n"
                +"    //@ assert FIELD.length == 5 ;\n"
                +"    //@ assert FIELD2.length == 6 ;\n"
                +"    //@ assert H.CHILD.length == 5 ;\n"
                +"    //@ assert H.CHILD2.length == 6 ;\n"
                +"  }\n"
                +"}\n"
                +" class H  { \n"
                +"  public /*@ final */ static int ZZZZ = 79;\n"
                +"  public /*@ final */ static int[] CHILD = new int[]{1,2,3,4,5};\n"
                +"  public /*@ final */ static int[] CHILD2 = {1,2,3,4,5,6};\n"

                +"  //@ public normal_behavior ensures true; static_initializer\n"
                +"}\n"
                );
        
        }
    
    @Test 
    public void testDeterminism() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"
                
                +"  //@ ensures true;\n"
                +"  //@ model pure public int mm(int i);\n"
                
                +"  //@ ensures true; pure\n"
                +"  public int mmr(int i) { return 0; };\n"
                
                +"  //@ ensures !\\fresh(\\result); pure\n"
                +"  //@ model public <TT> TT mt(int i);\n"
                
                +"  //@ ensures !\\fresh(\\result); pure\n"
                +"  public /*@ nullable */ <TT> TT mtr(int i) { return null; };\n"
                
                +"  //@ ensures true; pure\n"
                +"  //@ model function public static int mf(int i);\n"
                
                +"  //@ ensures true; pure\n"
                +"  //@ function \n"
                +"  public static int mfr(int i) { return 0; }\n"
                
                +"  //@ ensures mm(i) == mm(i);\n"
                +"  public void m1(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures mmr(i) == \\result;\n"
                +"  public int m1x(int i) {\n"   // Line 20
                +"      return mmr(i);\n"
                +"  }\n"
                
                +"  //@ ensures mt(i) == mt(i);\n"
                +"  public void m3(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures mtr(i) == \\result;\n"
                +"  public /*@ nullable */ <T> T m3x(int i) {\n"
                +"    return mtr(i); }\n"   // Line 28
                
                +"  //@ ensures mf(i) == mf(i);\n"
                +"  public void m2(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures mfr(i) == \\result;\n"
                +"  public int m2x(int i) {\n"
                +"      return mfr(i);\n"
                +"  }\n"
                
               
                +"}"
                );
    }

    @Test 
    public void testDeterminismFresh() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"
        		+"  public /*@ nullable */ Object o;\n"
                
                +"  //@ ensures \\fresh(\\result); pure\n"
                +"  public Object mm(int i) { return new Object(); }\n"
                
   //             +"  //@ ensures \\result == null || !\\fresh(\\result); pure\n" // FIXME - should this work -= does not prevent the result from being fresh for m2 while not for mm2 
                +"  //@ ensures \\result == o; pure\n" 
                +"  public /*@ nullable */ Object mm2(int i) { return o; }\n" // Line 7
                
                +"  //@ ensures true; pure\n"
                +"  public Object mm3(int i) { return new Object(); }\n"
                
                 
                +"  //@ ensures \\fresh(\\result);\n"  // Line 10 
                +"  //@ ensures mm(i) == \\result;\n" // ERROR - not necessarily the case
                +"  public Object m1(int i) {\n" 
                +"      return mm(i);\n"   // Line 13
                +"  }\n"
                
                +"  //@ ensures \\result == null || !\\fresh(\\result);\n"
                +"  //@ ensures mm2(i) == \\result;\n" 
                +"  public /*@ nullable */ Object m2(int i) {\n" 
                +"      return mm2(i);\n"
                +"  }\n"
                
                +"  //@ ensures mm3(i) == \\result;\n" // Line 20 // ERROR - not necessarily the case
                +"  public Object m3(int i) {\n" 
                +"      return mm3(i);\n"
                +"  }\n"
                
               
                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Postcondition) in method m1",7
                ,"/tt/TestJava.java:11: warning: Associated declaration",7
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Postcondition) in method m3",7
                ,"/tt/TestJava.java:20: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testMethodMatching() {
        main.addOptions("-method=mm"); // Part of test
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"
                +"   int k;\n"
                +"  //@ ensures true; pure \n"
                +"  public int mpure(int i) { return i+17; }\n"
                
                +"  public void mm(int i) { \n"
                +"     int j = 0; \n"
                +"     if (i == 1) j = mpure(i); \n"
                +"     else if (i == 2) { j = mpure(i);  } \n"
                +"     else  j = 29; \n"
                +"     //@ assert i==1 ==> j == mpure(1); \n"
                +"     //@ assert i==2 ==> j == mpure(2); \n"
                +"     //@ assert i==3 ==> j == mpure(1); \n" // CAN'T PROVE
                +"     //@ assert i==3 ==> j != mpure(1); \n" // CAN'T PROVE
                
                +"  }\n"
                
                
               
                +"}"
                ,anyorder(
                 seq("/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                )
                );
    }

    @Test
    public void testMethodMatching1() {
        main.addOptions("-method=mm"); // Part of test
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"
                +"   int k;\n"
                +"  //@ ensures true; pure \n"
                +"  public int mpure(int i) { return i+17; }\n"
                
                +"  public void mm(int i) { \n"
                +"     int j = 0; \n"
                +"     if (i == 1) j = mpure(i); \n"
                +"     else if (i == 2) { j = mpure(i); k = 0; } \n"
                +"     else  j = 29; \n"
                +"     //@ assert i==1 ==> j == mpure(1); \n" // CAN'T PROVE
                +"     //@ assert i==2 ==> j == mpure(2); \n" // CAN'T PROVE
                +"     //@ assert i==3 ==> j == mpure(1); \n" // CAN'T PROVE
                +"     //@ assert i==3 ==> j != mpure(1); \n" // CAN'T PROVE
                
                +"  }\n"
                
                
               
                +"}"
                ,anyorder(
                 seq("/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                ,seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method mm",10)
                )
                );
    }

    @Test
    public void testExplicitAssert() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m1ok(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  public void m1okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  public void m2bad(int i) {\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  public void m2badb(int i) {\n"  // Line 20
                +"    assert i == 0 : \"m2badb fails\" ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m2ok(int i) {\n"
                +"    assert i == 0 : \"ASD\" ;\n"
                +"  }\n"
                
                +"  public void m2okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m2bad",5
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method m2badb: m2badb fails",5
                );
    }
    
    @Test
    public void testUndefined() {
        main.addOptions("-logic=AUFNIRA");
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        if ("cvc4".equals(solver)) return; // SKIPPING cvc4 does not handle integer division
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires 10/i < 0;\n"
                +"  public void m1bad(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i != 0 && 10/i < 0;\n"
                +"  public void m1good(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures 10/i < 0 || true;\n"
                +"  public void m2bad(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 || 10/i < 0 || true;\n"
                +"  public void m2good(int i) {\n"
                +"  }\n"
                
                +"  public void m3bad(int i) {\n"
                +"  //@ assume 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m3good(int i) {\n"
                +"  //@ assume i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m4bad(int i) {\n"
                +"  //@ assert 10/i < 0 ||true;\n"
                +"  }\n"
                
                +"  public void m4good(int i) {\n"
                +"  //@ assert i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m5bad(int i) {\n"
                +"  //@ assert 10%i < 0 ||true;\n"
                +"  }\n"
                
                +"  public void m5good(int i) {\n"
                +"  //@ assert i == 0 || 10%i < 0 || true;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m2bad",17
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m3bad",16
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4bad",16
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5bad",16
                );    }


    @Test
    public void testControl() {
        main.addOptions("-code-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  int x,xx; static int y,yy; \n"
                
                +"  public void m1good() {\n"
                +"    for (int i=0; i<10; i=i+1) {\n"
                +"       //@ assert i<10;\n"
                +"    }\n"
                +"  }\n"
                                
                +"  public void m2good() {\n"
                +"    int i=0; \n"
                +"    while (i<10) {\n"
                +"       //@ assert i<10;\n"
                +"       i = i + 1;\n"
                +"    }\n"
                +"    //@ assert i>=10;\n"
                +"  }\n"
                                
                +"  public void m2bad() {\n"
                +"    int i=0; \n"
                +"    while (i<10) {\n"
                +"       //@ assert i<10;\n"
                +"       i = i + 1;\n"
                +"    }\n"
                +"    //@ assert i>10;\n"
                +"  }\n"

                // FIXME - fix the assumptions here - first time through loop
//                +"  public void m3good() {\n"
//                +"    int i=0; \n"
//                +"    do {\n"
//                +"       //@ assert i<10;\n"
//                +"       i = i + 1;\n"
//                +"       //@ assert i<=10;\n"
//                +"    } while (i<10); \n"
//                +"    //@ assert i>=10;\n"
//                +"  }\n"
//                                
//                +"  public void m3bad() {\n"
//                +"    int i=0; \n"
//                +"    do {\n"
//                +"       //@ assert i<10;\n"
//                +"       i = i + 1;\n"
//                +"       //@ assert i<=10;\n"
//                +"    } while (i<10); \n"
//                +"    //@ assert i>10;\n"
//                +"  }\n"
                                
                +"  //@ requires arg != null; \n"
                +"  public void m4good(int[] arg) {\n"
                +"    int i=0; \n"
                +"    for (int k: arg) {\n"
                +"       i = i + 1;\n"
                +"    }  \n"
                +"    // FIXME //@ assert i == arg.length;\n"
                +"  }\n"
                                
                +"  //@ requires arg != null; \n"
                +"  public void m4bad(int[] arg) {\n"
                +"    int i=0; \n"
                +"    for (int k: arg) {\n"
                +"       i = i + 1;\n"
                +"    }  \n"
                +"    //@ unreachable;\n"
                +"  }\n"
                                
                                
                +"}"
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (Unreachable) in method m4bad",9
                );
        }

    @Test 
    public void testConstantFolding() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"

                // FIXME - lots more tests needed
                +"  public void mm(int i) {\n" 
                +"      boolean b = true && false;\n" 
                +"      //@ assert !b;\n" 
                +"      b = true || false;\n" 
                +"      //@ assert b;\n" 
                
                +"      b = true == false;\n" 
                +"      //@ assert !b;\n" 
                +"      b = true != false;\n" 
                +"      //@ assert b;\n" 
                +"      b = 3L != 2;\n" 
                +"      //@ assert b;\n" 
                +"      b = (short)3 == (short)3;\n" 
                +"      //@ assert b;\n" 
                +"      b = \"\" == \"\";\n" 
                +"      //@ assert b;\n" 
                +"      b = ' ' == ' ';\n" 
                +"      //@ assert b;\n" 
                
                +"      int a = 2 + 3;\n" 
                +"      //@ assert a == 5;\n" 
                +"      a = (short)2 + (short)3;\n" 
                +"      //@ assert a == 5;\n" 
                +"      long g = 2L + 3;\n" 
                +"      //@ assert g == 5;\n" 
                +"      g = (short)2 + (short)3;\n" 
                +"      //@ assert g == 5;\n" 
                
                +"      a = (short)3 / (short)2;\n" 
                +"      //@ assert a == 1;\n" 
                +"      g = 3L / 2;\n" 
                +"      //@ assert g == 1;\n" 
                +"      g = (short)3 / (short)2;\n" 
                +"      //@ assert g == 1;\n" 
                
//                +"      String s = \"x\" + \"y\";\n" 
//                +"      //@ assert s = \"xy\";\n" 
//                +"      s = \"x\" + 1;\n" 
//                +"      //@ assert s = \"x1\";\n" 
//                +"      s = \"x\" + true;\n" 
//                +"      //@ assert s = \"xtrue\";\n" 
//                +"      s = false + \"x\";\n" 
//                +"      //@ assert s = \"falsex\";\n" 
//                +"      s = \"x\" + null;\n" 
//                +"      //@ assert s = \"xnull\";\n" 

                +"  }\n"
                
               
                +"}"
                );
    }

    @Test 
    public void testConstantFolding4() {
        main.addOptions("-method=mm","-show=translated");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ requires a.length > 10;\n" 
                +"  public void mm(int[] a) {\n" 
                +"      int x = a[2];\n" 
                +"      int[] z = new int[3];\n" 
                +"      //@ ghost boolean b = Integer.class <: Number.class;\n" 
                +"      //@ ghost boolean bb = Number.class <: Boolean.class;\n" 
                +"      //@ assert b && !bb;\n"
                +"  }\n"
                
               
                +"}"
                );
    }

    @Test 
    public void testConstantFolding3() {
        main.addOptions("-method=mm","-show=translated");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void mm() {\n" 
                +"      m(Integer.class);\n" 
                +"      m(Boolean.class);\n" 
                +"      m(Short.class);\n" 
                +"  }\n"
                +"  public static int j;\n" 
                +"  //@ requires clazz <: Number.class;\n" 
                +"  //@ assignable j;\n" 
                +"  //@ ensures j > 100;\n" 
                +"  //@ also\n" 
                +"  //@ requires clazz <: Boolean.class;\n" 
                +"  //@ assignable j;\n" 
                +"  //@ ensures j > 200;\n" 
                +"  //@ also\n" 
                +"  //@ requires clazz <: String.class;\n" 
                +"  //@ assignable j;\n" 
                +"  //@ ensures j > 200;\n" 
                +"  public static  void m( Class<?> clazz) {\n" 
                +"    j = 1000;\n"
                +"  }\n"
                
               
                +"}"
                );
    }


    @Test 
    public void testConstantFolding5() {
 //       main.addOptions("-method=mm","-show=translated");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void mm() {\n" 
                +"      m(1);\n" 
                +"      m(2);\n" 
                +"  }\n"
                +"  public int j;\n" 
                +"  //@ requires i > 0;\n" 
                +"  //@ assignable j;\n" 
                +"  //@ ensures j > 100;\n" 
                +"  //@ also\n" 
                +"  //@ requires i >= 2;\n" 
                +"  //@ assignable j;\n" 
                +"  //@ ensures j > 200;\n" 
                +"  public void m(int i) {\n" 
                +"    j = 1000;\n"
                +"  }\n"
                
               
                +"}"
                );
    }

    @Test 
    public void testConstantFolding2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"

                // FIXME - lots more tests needed
                +"  public void mm(int i) {\n" 
                +"      int a = 2 / 1;\n" 
                +"      a = 2 / (1-1);\n" 
                +"      long g = 3L / 0;\n" 
                +"  }\n"
                
               
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method mm",13
                );
    }

    @Test 
    public void testRefactoring() {
        expectedExit = 0;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void mm(int i) {\n" 
                +"      int a = 2;\n" 
                +"      {\n" 
                +"      //#-\n" 
                +"      a++;\n" 
                +"      //#-\n" 
                +"      a+=3;\n" 
                +"      //# a += 2;\n" 
                +"      }\n" 
                +"      //@ assert a == 7;\n" 
                +"  }\n"
                
                +"  public void mok2(int i) {\n" 
                +"      int a = 2;\n" 
                +"      {\n" 
                +"      //#-\n" 
                +"      a++;\n" 
                +"      //# a += 2;\n" 
                +"      }\n" 
                +"      //@ assert a == 4;\n" 
                +"  }\n"
                
//                +"  public void mbad2(int i) {\n" 
//                +"      int a = 2;\n" 
//                +"      {\n" 
//                +"      //#-\n"   // TODO - should warn about skipping the rest of the input
//                +"      a++;\n" 
//                +"      }\n" 
//                +"      //@ assert a == 4;\n" 
//                +"  }\n"
                
               
                +"}"
                );
    }

    @Test 
    public void testPreconditionInfo() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> { \n"

                +"  //@ requires i == 4;\n" 
                +"  //@ ensures \\result == 5;\n" 
                +"  //@ also\n" 
                +"  //@ requires i == 5;\n" 
                +"  //@ ensures \\result == 6;\n" 
                +"  /*@ pure */ public int m(int i) {\n" 
                +"     return i + 1;\n"
                +"  }\n"
                
                +"  public void mm(int i) {\n" 
                +"  //@ assert 0<m(3);\n" 

                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method mm",17
                ,"/tt/TestJava.java:8: warning: Associated declaration",26
                ,optional(
                "/tt/TestJava.java:3: warning: Precondition conjunct is false: i == 4",18
                ,"/tt/TestJava.java:6: warning: Precondition conjunct is false: i == 5",18
                )
                
               
                );
    }

    @Test 
    public void testOldInAssign() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +" public int f;\n" 
                +" public int[] a = new int[10];\n" 

                +"  //@ old int j = i+2;\n" 
                +"  //@ requires 0 <= j && j < 10;\n" 
                +"  //@ requires a != null && a.length == 10;\n" 
                +"  //@ assignable a[j];\n" 
                +"  //@ ensures a[j] == 42;\n" 
                +"  public void m(int i) {\n" 
                +"     a[i+2] = 42;\n"
                +"  }\n"
                
                +"  //@ requires 0 <= i && i < 8;\n" 
                +"  //@ requires a != null && a.length == 10;\n" 
                +"  //@ assignable a[i];\n" 
                +"  public void m1bad(int i) {\n" 
                +"     i += 2; a[i] = 42;\n"
                +"  }\n"
                
                +"  //@ requires 0 <= i && i < 8;\n" 
                +"  //@ requires a != null && a.length == 10;\n" 
                +"  //@ assignable a[i+2];\n" 
                +"  public void m2(int i) {\n" 
                +"     i += 2; a[i] = 42;\n"
                +"  }\n"
                
                +"  //@ old int j = i+1;\n" 
                +"  //@ requires 0 <= j && j < 9;\n" 
                +"  //@ requires a != null && a.length == 10;\n" 
                +"  //@ assignable a[j];\n" 
                +"  public void mbad(int i) {\n" 
                +"     a[i+2] = 42;\n"
                +"  }\n"
                

                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assignable) in method m1bad:  a[i]",19
                ,"/tt/TestJava.java:15: warning: Associated declaration",7
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Assignable) in method mbad:  a[i + 2]",13
                ,"/tt/TestJava.java:28: warning: Associated declaration",7
                
               
                );
    }

    @Test 
    public void testOldInCall() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +" public int f;\n" 
                +" public int[] a = new int[100];\n" 

                +"  //@ old int j = i+off;\n" 
                +"  //@ requires a != null && a.length == 100;\n" 
                +"  //@ requires 0 <= i && i < 50 && 0 <= off && off < 30;\n" 
                +"  //@ assignable a[j];\n" 
                +"  public void mmm(int i, int off) {\n" 
                +"     a[i+off] = 42;\n"
                +"  }\n"
                
                +"  //@ requires 0 <= i && i < 50;\n" 
                +"  //@ requires a != null && a.length == 100;\n" 
                +"  //@ assignable a[i],a[i+10],a[i+25];\n" 
                +"  public void m(int i) {\n" 
                +"     mmm(i,0);\n"
                +"     mmm(i,10);\n"
                +"     mmm(i,25);\n"
                +"  }\n"
                


                +"}"
                );
    }

    @Test 
    public void testConcat() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ requires s1.length() + s2.length() <= Integer.MAX_VALUE;\n"
                +"  public void m1(String s1, String s2) {\n" 
                +"     String s = s1 + s2;\n"
                +"     //@ assert s.length() == s1.length() + s2.length();\n"
                +"  }\n"
                
                +"  //@ requires s1.length() < Integer.MAX_VALUE;\n"
                +"  public void m2(String s1, String s2) {\n" 
                +"     String s = s1 + String.valueOf('c');\n"
                +"     //@ assert s.length() == s1.length() + 1;\n"
                +"  }\n"
                
                +"  //@ requires s1.length() < Integer.MAX_VALUE;\n"
                +"  public void m2a(String s1, String s2) {\n" 
                +"     String s = s1 + Character.toString('c');\n"
                +"     //@ assert s.length() == s1.length() + 1;\n"
                +"  }\n"
                
                +"  //@ requires s1.length() < Integer.MAX_VALUE;\n"
                +"  public void m3(String s1, String s2) {\n" 
                +"     String s = s1 + 'c';\n"
                +"     //@ assert s.length() == s1.length() + 1;\n"
                +"  }\n"
                +"}"
                );
    }


    @Test 
    public void testLongShift() {
        main.addOptions("-code-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void m1(long x) {\n" 
                +"     int y = (int)x;\n"
                +"     long yy = y < 0 ? ((long)y-Integer.MIN_VALUE-Integer.MIN_VALUE) : y;\n"
                +"     int z = (int)(x>>32);\n"
                +"     long w = (((long)z)<<32) + yy;\n"
                +"     long zzz = (x>>>32);\n"
                +"     int zz = (int)(x>>>32);\n"
                +"     long ww = (((long)zz)<<32) + yy;\n"
                +"     //@ show x, y, z, zzz, zz, yy, w, ww;\n"
                +"     //@ assert w == x;\n"
                +"     //@ assert ww == x;\n"
                +"  }\n"
                
                +"}"
                );
    }


}
