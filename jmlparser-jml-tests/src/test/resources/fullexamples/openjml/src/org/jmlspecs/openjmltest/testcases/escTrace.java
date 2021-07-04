package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escTrace extends EscBase {
    
    public escTrace(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        captureOutput = true;
        super.setUp();
        main.addOptions("-subexpressions");
    }
 
    public static final String dir = "test/escTraceTests";

    /** This String declaration and assignment */
    @Test
    public void testSimpleTrace() {
        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math */ public class TestJava { \n"
                
                +"  public void m1(int i) {\n"
                +"       int j = 5;\n"
                +"       j = j + i;\n"
                +"       //@ assert j != 7;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);
        
        outputCompare.compareTextToMultipleFiles(output, dir, "testSimpleTrace-expected", dir + "/testSimpleTrace-actual");
   }

    // FIXME - the ??? is the trace values
    
    /** This String declaration and assignment */
    @Test
    public void testFieldTrace() {
        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math */ public class TestJava { \n"
                +"       int k;\n"
                
                +"  public void m1(int i) {\n"
                +"       k = 5 + i;\n"
                +"       //@ assert k != 7;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1",12
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);
        outputCompare.compareTextToMultipleFiles(output, dir, "testFieldTrace-expected", dir + "/testFieldTrace-actual");
       //Assert.assertEquals(expectedOut,output);
    }

    /** This String declaration and assignment */
    @Test
    public void testEnsuresTrace() {
        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_java_math */ public class TestJava { \n"
                +"       int k;\n"
                
                +"  //@ requires i == 1;\n"
                +"  //@ ensures \\result < i-i;\n"
                +"  public int m1(int i) {\n"
                +"       k = 5 + i;\n"
                +"       return k * 2;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m1",8
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
        String output = output();
        String error = errorOutput();
        Assert.assertEquals("Mismatched error output","",error);
        outputCompare.compareTextToMultipleFiles(output, dir, "testEnsuresTrace-expected", dir + "/testEnsuresTrace-actual");
       //Assert.assertEquals(expectedOut,output);
    }

    /** This String declaration and assignment */
    @Test
    public void testEnsuresSafeTrace() {
        main.addOptions("-method=m1"); // Part of test
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ code_safe_math */ public class TestJava { \n"
                +"       int k;\n"
                
                +"  //@ requires i == Integer.MAX_VALUE;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public int m1(int i) {\n"
                +"       k = 5 + i;\n"
                +"       return k;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m1:  overflow in int sum",14
                );
        String output = output();
        String error = errorOutput();
        outputCompare.compareTextToMultipleFiles(output, dir, "testEnsuresSafeTrace-expected", dir + "/testEnsuresSafeTrace-actual");
        Assert.assertEquals("Mismatched error output","",error);
       //Assert.assertEquals(expectedOut,output);
    }

}