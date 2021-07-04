package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escArithmeticModes extends EscBase {

    static boolean runLongArithmetic = runLongTests || System.getProperty("RUNLONGARITH") != null;

    static {
        if (runLongTests && !runLongArithmetic) System.out.println("Skipping long tests in escArithmeticModes");
    }


    @Parameters
    static public Collection<String[]> parameters() {
        String[] options = {"-escBV=true","-escBV=false"};
        return optionsAndSolvers(options,solvers);
    }


    public escArithmeticModes(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    @Test @Ignore // Times out in BV mode
    public void testNegNeg() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires i >= 0;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m(int i) {\n"
                +"    int k = -(-i);\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testNegJavaInt() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;\n"
                +"public class TestJava { \n"
                +"  //@ ensures i != 0x80000000 ==> \\safe_math(\\result + i) == 0;\n"                
                +"  //@ ensures i == 0x80000000 ==> \\result == i;\n"                
                +"  /*@ code_java_math spec_bigint_math */ public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testNegJavaLong() {  // Takes about 5 min in BV mode
        Assume.assumeTrue(runLongArithmetic || !options.contains("-escBV=true"));
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;\n"
                +"public class TestJava { \n"
                +"  //@ ensures i != 0x8000000000000000L ==> \\safe_math(\\result + i) == 0;\n"                
                +"  //@ ensures i == 0x8000000000000000L ==> \\result == i;\n"                
                +"  /*@ code_java_math */ public long ml(long i) {\n"
                +"    long k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testNegSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecBigintMath public class TestJava { \n"
                +"  //@ ensures i != 0x80000000 ==> \\safe_math(\\result + i) == 0;\n"                
                +"  //@ ensures i == 0x80000000 ==> \\result == i;\n"                
                +"  public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ ensures i != 0x8000000000000000L ==> \\safe_math(\\result + i) == 0;\n"                
                +"  //@ ensures i == 0x8000000000000000L ==> \\result == i;\n"                
                +"  public long ml(long i) {\n"
                +"    long k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ ensures \\safe_math(\\result + i) == 0;\n"                
                +"  public int mm(short i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  (int negation)",13
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ml:  (long negation)",14
              );
    }

    @Test
    public void testNegMath() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;\n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ ensures \\safe_math(\\result + i) == 0;\n"                
                +"  public int m(int i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ ensures \\safe_math(\\result + i) == 0;\n"                
                +"  public long ml(long i) {\n"
                +"    long k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ ensures \\safe_math(\\result + i) == 0;\n"                
                +"  public int ms(short i) {\n"
                +"    int k = -i;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method ml:  long overflow",14
              );
    }

    @Test
    public void testSumSafe1() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"   // ERROR
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  underflow in int sum",15)
                         ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  overflow in int sum",15))
              );
    }

    @Test
    public void testSumSafe2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int ma(int i) {\n"
                +"    //@ assume i <= 0x3FFFFFFF;\n"
                +"    int k = i + i;\n"   // ERROR
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  underflow in int sum",15
              );
    }

    @Test
    public void testSumSafe3() {
        Assume.assumeTrue(runLongArithmetic || !options.contains("-escBV=true"));
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= (int)(0xC0000000);\n"
                +"    int k = i + i;\n"    // ERROR
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method mb:  overflow in int sum",15
              );
    }

    @Test
    public void testSumSafe4() {
        Assume.assumeTrue(runLongArithmetic || !options.contains("-escBV=true"));
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  public int mc(int i) {\n"
                +"    //@ assume i <= 0x3FFFFFFF;\n"
                +"    //@ assume i >= (int)(0xC0000000);\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    //@ assume (i < 0) != (j < 0);\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testSumJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    int k = i + i;\n"
                +"    //@ assert k >= 0;\n" // Error
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method mb",9
              );
    }

    @Test
    public void testSumMath() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public long mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    long k = i + i;\n"  // OK
                +"    //@ assert k >= 0;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mm(int i, int j) {\n"
                +"    int k = i + j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
//                ,seq(
//                anyorder(
//                 seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
//                ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                ),anyorder(
//                 seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18)
//                ,seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int underflow",18)
//                ))
              );
    }

    @Test @Ignore // FIXME - still have to sort out how assignments are handled in Math mode
    public void testSumMathArg() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  @SkipEsc public long mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    long k = i + i;\n"  // OK
                +"    //@ assert k >= 0;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public long mq(int i, int j) {\n"
                +"    long k = mb(i + j);\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,seq(
                anyorder(
                 seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
                ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                ),anyorder(
//                 seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18)
//                ,seq("/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int underflow",18)
                ))
              );
    }

    @Test
    public void testSumMathB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i + i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  public int mb(int i) {\n"
                +"    //@ assume i >= 0;\n"
                +"    int k = (int)(i + i);\n"
                +"    //@ assert k >= 0;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
//                ,anyorder(
//                  seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int overflow",13)
//                 ,seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m:  int underflow",13)
//                 )
//                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mb:  int overflow",18
              );
    }

    @Test
    public void testDivJava() {
        Assume.assumeTrue(runLongArithmetic);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath public class TestJava { //@ requires j !=0 ; \n"
                +"  public int m(int i, int j) {\n"
                +"    int k = i/j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testDivSafe() {
        Assume.assumeTrue(runLongArithmetic);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath public class TestJava { \n"
                +"  //@ requires j !=0;\n"
                +"  public int m(int i, int j) {\n"
                +"    int k = i/j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  overflow in int divide",14
              );
    }

    @Test
    public void testDivMath() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n "
                +"  //@ requires j !=0;\n"
                +"  public long m(int i, int j) {\n"
                +"    long k = i/j;\n"
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }
    
    // FIXME - need to test long versions of Mult and perhaps everything else

    @Test
    public void testMultSafe() {
        Assume.assumeTrue(runLongArithmetic || !options.contains("-escBV=true"));
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public int m(int i) {\n"
                +"    int k = i * i;\n"   // ERROR
                +"    return k; \n"
                +"  }\n"
                +"  public int ma(int i) {\n"
                +"    //@ assume i <= 30000 && i >= -30000;\n"
                +"    int k = i * i;\n"  // OK
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == 605032704;\n"
                +"  public int mc(int i) {\n"
                +"    int k = i * i;\n"   // ERROR
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 30000;\n"
                +"  //@ ensures \\result == 900000000L;\n"
                +"  public long me(int i) {\n"
                +"    long k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method m:  int multiply overflow",15
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method mc:  int multiply overflow",15
              );
    }

    @Test
    public void testMultJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m(int i) {\n"
                +"    long k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"  public int ma(int i) {\n"
                +"    //@ assume i <= 30000 && i >= -30000;\n"
                +"    int k = i * i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == 605032704L;\n"
                +"  public int mc(int i) {\n"
                +"    int k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == -605032704L;\n"
                +"  public int md(int i) {\n"
                +"    int k = -i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == -605032704L;\n"
                +"  public long mdd(int i) {\n"
                +"    long k = -i * i;\n" //  multiplication is just 32 bit, but no overflow warning  
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 30000;\n"
                +"  //@ ensures \\result == 900000000L;\n"
                +"  public long me(int i) {\n"
                +"    long k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testMultMath() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath public class TestJava { \n"
                +"  public long m(int i) {\n"
                +"    long k = i * i;\n" 
                +"    return k; \n"
                +"  }\n"
                +"  public int ma(int i) {\n"
                +"    //@ assume i <= 30000 && i >= -30000;\n"
                +"    int k = i * i;\n"
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == 4900000000L;\n"
                +"  public int mc(int i) {\n"
                +"    int k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == -4900000000L;\n"
                +"  public int md(int i) {\n"
                +"    int k = -i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"  //@ requires i == 70000;\n"
                +"  //@ ensures \\result == 4900000000L;\n"
                +"  public long me(int i) {\n"
                +"    long k = i * i;\n"   
                +"    return k; \n"
                +"  }\n"
                +"}\n"
//                ,anyorder(seq("/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method mc:  int overflow",13)
//                ,seq("/tt/TestJava.java:21: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method md:  int underflow",21)
//                )
              );
    }


}

