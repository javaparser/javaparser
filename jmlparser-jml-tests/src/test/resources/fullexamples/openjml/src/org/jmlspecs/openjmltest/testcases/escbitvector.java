package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

//FIXME _ need to test when inline body is in separate file
//FIXME _ need to test when inline body is in separate file that is not parsed on the command-line
// FIXME - need to test when inline is in .jml
// FIXME - need to test when inline is in .jml for a binary class

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escbitvector extends EscBase {

    public escbitvector(String options, String solver) {
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
    
    // auto BV, with precondition
    @Test 
    public void testBV2() {
        main.addOptions("-escBV=auto","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    // BV true, with precondition (sometimes times out)
    @Test 
    public void testBV2a() {
        main.addOptions("-escBV=true","-logic=ALL","-solver-seed=42");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    // BV true, with precondition and modulo operation
    @Test 
    public void testBV2b() {
        Assume.assumeTrue(runLongTests);
        main.addOptions("-escBV=true","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result%16) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    // default BV, no precondition
    @Test 
    public void testBV1() {
        Assume.assumeTrue(runLongTests);
        main.addOptions("-logic=ALL");  // Should use BV
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"  // FAILS for very large n, e.g. Integer.MAX_VALUE
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    
    // BV off
    @Test 
    public void testBV1b() {
        expectedExit = 0;
        main.addOptions("-escBV=false","-logic=ALL");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires n <= Integer.MAX_VALUE-15;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    // incorrect escBV option
    @Test 
    public void testBVe1() {
        main.addOptions("-escBV","-logic=ALL"); // Testing incorrect use of -escBV
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return 0;\n"
                +"  }\n"
                                
                +"}"
                ,"warning: Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: -logic=ALL",-1
          );
    }
    
    // incorrect escBV option
    @Test 
    public void testBVe2() {
        main.addOptions("-escBV=xx","-logic=ALL");  // This should cause an error
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return 0;\n"
                +"  }\n"
                                
                +"}"
                ,"warning: Command-line argument error: Expected 'auto', 'true' or 'false' for -escBV: xx",-1
         );
    }
    
    // OK option, with precondition
    @Test 
    public void testBVe3() {
        main.addOptions("-escBV=","-logic=ALL");  // Should revert to auto
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
          );
    }
    
    // another incorrect use of escBV option
    @Test 
    public void testBVe4() {
        expectedExit = 0;
        main.addOptions("-escBV");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires n <= 0x7ffffff0;\n"
                +"  //@ ensures n <= \\result;\n"
                +"  //@ ensures \\result <= n+15;\n"
                +"  //@ ensures (\\result&15) == 0;\n"
                +"  //@ pure\n"
                +"//@ code_java_math spec_java_math\n"
                +"  public int m1(int n) {\n"
                +"    return n + ((-n) & 0x0f);\n"
                +"  }\n"
                                
                +"}"
                ,"warning: The last command-line option expects a parameter: -escBV",-1
          );
    }
    
    // Simple use of explicit BV auto
    @Test
    public void testBVauto() {
        // This test first tries SMT translation without BV, which fails, and then it tries with, and succeeds.
        expectedExit = 0;
        main.addOptions("-escBV=auto","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +" class A { \n"
                +"   //@ requires (i&5) == 1; pure \n"
                +"   public static boolean mm(int i) { return true; } \n"
                +"}\n"
                
                +" public class TestJava { \n"
                +"  //@ requires A.mm(1);\n"
                +"  public void m1() {\n"
                +"  }\n"
                                
                +"}"
          );
    }
    
    // Simple use of explicit BV false
    @Test
    public void testBVauto2() {
        // This test, the same code as above, only tries SMT translation without BV, which fails.
        expectedExit = 1;
        main.addOptions("-escBV=false","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +" class A { \n"
                +"   //@ requires (i&5) == 1; pure \n"
                +"   public static boolean mm(int i) { return true; } \n"
                +"}\n"
                
                +" public class TestJava { \n"
                +"  //@ requires A.mm(1);\n"
                +"  public void m1() {\n"
                +"  }\n"
                                
                +"}"  // FIXME - Message repeats for mm and m1, but why optional, why not indicate which method?
                ,"/tt/TestJava.java:3: This method uses bit-vector operations and must be run with -escBV=true (or auto) [Bit-operation BITAND]",19
                ,optional("/tt/TestJava.java:3: This method uses bit-vector operations and must be run with -escBV=true (or auto) [Bit-operation BITAND]",19)
          );
    }
    
    // Simple use of explicit BV true
    @Test
    public void testBVauto3() {
        // This test, the same code as above, only tries SMT translation with BV the first time.
        expectedExit = 0;
        main.addOptions("-escBV=true","-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +" class A { \n"
                +"   //@ requires (i&5) == 1; pure \n"
                +"   public static boolean mm(int i) { return true; } \n"
                +"}\n"
                
                +" public class TestJava { \n"
                +"  //@ requires A.mm(1);\n"
                +"  public void m1() {\n"
                +"  }\n"
                                
                +"}"
          );
    }
    

}
