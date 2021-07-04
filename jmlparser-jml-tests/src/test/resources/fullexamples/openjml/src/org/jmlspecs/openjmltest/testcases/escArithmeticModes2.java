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
public class escArithmeticModes2 extends EscBase {

    static boolean runLongArithmetic = runLongTests || System.getProperty("RUNLONGARITH") != null;
    
    @Parameters
    static public Collection<String[]> parameters() {
        String[] options = {"-escBV=false","-escBV=true","-escBV=auto"};
        return optionsAndSolvers(options,solvers);
    }
    
    static {
        if (runLongTests && !runLongArithmetic) System.out.println("Skipping long tests in escArithmeticModes2");
    }


    public escArithmeticModes2(String options, String solver) {
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
 
    // Checks the value and sign of int division and mod
    @Test 
    public void testModJava() {
        Assume.assumeTrue(runLongArithmetic);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    // Checks the value and sign of int division and mod
    @Test
    public void testModJavaZ() {
        Assume.assumeTrue(runLongArithmetic);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    // Checks the value and sign of int division and mod
    @Test
    public void testModJava3() {
        Assume.assumeTrue(runLongArithmetic);
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public long m() {\n"
                +"    int k = - 2147483648 ;\n" 
                +"    int j = - 1073740802;\n" 
                +"    int m = - 2044;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    return k; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModJavaB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true"));
        //main.addOptions("-method=ma","-show","-subexpressions");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecJavaMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires j != -1 || i != 0x80000000;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int q = i/j; int r = i%j; int k = q * j + r;\n"
                +"    //@ show i, j, q, r, k;\n"
                +"    //@ assert (\\lbl KK (q * j + r)) == i; \n"
                +"    //@ assert k == i; \n"
                +"    //@ assert (\\lbl QQ (i/j)) * j + (\\lbl RR (i%j)) == i; \n"
                +"  }\n"
                +"  //@ requires i == 0x80000000 && j == -8322579;\n public void mm(int i, int j) { int q = i/j; int r = i%j; //@ show q, r; assert false; \n}\n"
                +"}\n"
              );
    }

    @Test
    public void testModSafe() {
        Assume.assumeTrue(runLongArithmetic || !options.contains("-escBV=true"));
        main.addOptions("-solver-seed=142");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }

    @Ignore // FIXME - times out
    @Test
    public void testModSafeZ() {
        Assume.assumeTrue(runLongArithmetic || !(options.contains("-escBV=true")||options.contains("-escBV=auto")));
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }


    @Ignore // FIXME - non-linear arithmetic has bad models
    @Test
    public void testModSafeB() {
        //main.addOptions("-show","-method=ma","-subexpressions");
        //Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Very long - skip for now
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  //@ requires j != 0 && i > 0 && j > 0;\n"
                +"  //@ requires j != -1 || i != 0x80000000;\n"
                +"  public void ma(int i, int j) {\n"
                +"    //@ show i, j; \n"
                +"    int q = (i/j) ;\n"
                +"    int m = (i%j) ;\n"
                +"    //@ show q, m; \n"
                +"    int k = q * j + m;\n"
                +"    //@ assert (\\lbl K k) == (\\lbl I i); \n"
                +"    //@ assert (\\lbl SUM (\\lbl PROD (\\lbl D ((\\lbl I i)/(\\lbl J j)))*(\\lbl JJ j)) + (\\lbl M (i%j))) == i; \n"  // not OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModSafeBB() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Very long - skip for now - TODO

        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i/j) * j + (i%j);\n"
                +"    //@ show i,j, k, i/j, i%j, (i/j) * j + (i%j); \n"
                +"    //@ assert k == i; \n"
                +"    //@ assert (i/j) * j + (i%j) == i; \n"
                +"  }\n"
                +"}\n"   // FIXME - not sure why the multiply overflow is sometimes not reported
                ,anyorder(
                   seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  overflow in int divide",15)
                  ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ArithmeticOperationRange) in method ma:  int multiply overflow",19)
                )
              );
    }

    @Test
    public void testModMath() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 7 ;\n" 
                +"    int j = 3;\n" 
                +"    int m = 1;\n" 
                +"    int qq = 2;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }
    
    @Test
    public void testModMathZ() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public void m() {\n"
                +"    int k = 15 ;\n" 
                +"    int j = 5;\n" 
                +"    int m = 0;\n" 
                +"    int qq = 3;\n" 
                +"    int i = k % j;\n" 
                +"    int q = k / j;\n" 
                +"    //@ assert i == m && q == qq ;\n" 
                +"    //@ assert (k%j) == m && (k/j) == qq;\n" 
                +"    i = (-k) % j;\n" 
                +"    q = (-k) / j;\n" 
                +"    //@ assert i == -m && q == -qq;\n" 
                +"    //@ assert ((-k)%j) == -m && ((-k)/j) == -qq;\n"   // Line 15
                +"    i = k % -j;\n" 
                +"    q = k / -j;\n" 
                +"    //@ assert i == m && q == -qq;\n" 
                +"    //@ assert (k%-j) == m && (k/-j) == -qq;\n" 
                +"    i = -k % -j;\n"                                   // Line 20
                +"    q = -k / -j;\n" 
                +"    //@ assert i == -m && q == qq;\n" 
                +"    //@ assert (-k%-j) == -m && ((-k)/-j) == qq;\n" 
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModMathB() {
        Assume.assumeTrue(runLongArithmetic && !options.contains("-escBV=auto"));
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int q,m; int k = (q=i/j) * j + (m=i%j);\n"
                +"    //@ show i,j,k,q,m,i/j,i%j; assert k == i; \n"
                +"    //@ assert (i/j) * j + (i%j) == i; \n"
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModEqual() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i%j);\n"
                +"    int m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m); \n"  // mnot OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: Label K has value 0",31
                ,"/tt/TestJava.java:8: warning: Label I has value ( - 2147483648 )",31
                ,"/tt/TestJava.java:8: warning: Label J has value ( - 1 )",42
                ,"/tt/TestJava.java:8: warning: Label D has value 2147483648",22
                ,"/tt/TestJava.java:8: warning: Label M has value ( - 2147483648 )",58
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method ma",9
                
              );
    }

    @Test
    public void testModEqualB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != 0x80000000 || j != -1;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int k = (i%j);\n"
                +"    int m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (i/j) == (\\lbl M m); \n"  // OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }

    @Test
    public void testModEqualLong() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(long i, long j) {\n"
                +"    long k = (i%j);\n"
                +"    long m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (\\lbl D ((\\lbl I i)/(\\lbl J j))) == (\\lbl M m); \n"  // mnot OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: Label K has value 0",31
                ,"/tt/TestJava.java:8: warning: Label I has value ( - 9223372036854775808 )",31
                ,"/tt/TestJava.java:8: warning: Label J has value ( - 1 )",42
                ,"/tt/TestJava.java:8: warning: Label D has value 9223372036854775808",22
                ,"/tt/TestJava.java:8: warning: Label M has value ( - 9223372036854775808 )",58
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method ma",9
                
              );
    }

    @Test
    public void testModEqualLongB() {
        Assume.assumeTrue(runLongArithmetic);
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != 0x8000000000000000L || j != -1;\n"
                +"  public void ma(long i, long j) {\n"
                +"    long k = (i%j);\n"
                +"    long m = (i/j);\n"
                +"    //@ assert (i%j) == (\\lbl K k); \n"  // OK
                +"    //@ assert (i/j) == (\\lbl M m); \n"  // OK for i = MIN && j = -1
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME
    @Test // Tests int multiplication in bigint mode
    public void testMult() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;\n"
                +"  public void ma(int i, int j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME
    @Test // Tests long multiplication in bigint mode
    public void testMultLong() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;\n"
                +"  public void ma(long i, long j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME - long running
    @Test // Tests int multiplication in java mode
    public void testMultJava() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;\n"
                +"  public void ma(int i, int j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME -- long running
    @Test // Tests long multiplication in java mode
    public void testMultJavaLong() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;\n"
                +"  public void ma(long i, long j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME - long running
    @Test // Tests int multiplication in safe mode
    public void testMultSafe() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Integer.MAX_VALUE && i*j >= Integer.MIN_VALUE;\n"
                +"  public void ma(int i, int j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME - long
    @Test // Tests long multiplication in safe mode
    public void testMultSafeLong() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i * j <= Long.MAX_VALUE && i*j >= Long.MIN_VALUE;\n"
                +"  public void ma(long i, long j) {\n"
                +"    //@ show i,j,i*j,(i*j)/j;\n"
                +"    //@ assert (i*j)/j == i;\n"
                +"    boolean b =  (i*j)/j == i;\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME - long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in bigint mode
    public void testDiv() {
        Assume.assumeTrue(!options.contains("-escBV=true")); // Cannot have BV and Math mode
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int q = i/j; //@ ghost int qq = i/j; \n"
                +"    int m = i%j;\n"
                +"    //@ show i,j,q,qq,m,i/j,i%j,j*q,j*(q+1),j*(q-1),j*q+m;\n"
                +"    if (i >= 0 && j >= 0) { /*@ assert q >= 0; assert i >= j*q; assert i-j < j*(q+1); assert m >= 0 && m < j; assert i == (j*q) + m; */ }\n"
                +"    if (i >= 0 && j < 0) { /*@ assert q <= 0; assert i >= j*q; assert i < j*(q-1);  assert m >= 0 && m < -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j >= 0) { /*@ assert q <= 0; assert i <= j*q; assert i > j*(q-1); assert m <= 0 && m > -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j < 0) { /*@ assert q >= 0; assert i <= j*q; assert i > j*(q+1); assert m <= 0 && m > j; assert i == (j*q) + m; */ }\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME -- long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in java mode
    public void testDivJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath @Options(\"-escMaxWarnings=1\") public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != Integer.MIN_VALUE || j != -1;\n"
                +"  public void ma(int i, int j) {\n"
                +"    int q = i/j;\n"
                +"    int m = i%j;\n"
                +"    //@ show i,j,q,m,j*q,j*(q+1),j*(q-1),j*q+m;\n"
                +"    if (i >= 0 && j >= 0) { /*@ assert q >= 0; assert i >= j*q; assert i < j*(q+1); assert m >= 0 && m < j; assert i == (j*q) + m; */ }\n"
                +"    if (i >= 0 && j < 0) { /*@ assert q <= 0; assert i >= j*q; assert i < j*(q-1);  assert m >= 0 && m < -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j >= 0) { /*@ assert q <= 0; assert i <= j*q; assert i > j*(q-1); assert m <= 0 && m < -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j < 0) { /*@ assert q >= 0; assert i <= j*q; assert i > j*(q+1); assert m <= 0 && m > j; assert i == (j*q) + m; */ }\n"
                +"  }\n"
                +"}\n"
              );
    }
    
    @Ignore // FIXME -- long running
    @Test  // Tests that div and mod give correct answers, if they do not overflow, in safe mode
    public void testDivSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath @Options(\"-escMaxWarnings=1\") public class TestJava { \n"
                +"  //@ requires j != 0;\n"
                +"  //@ requires i != Integer.MIN_VALUE || j != -1;\n"
               +"  public void ma(int i, int j) {\n"
               +"     //@ show i,j;\n"
               +"     int q = i/j;\n"
                +"    int m = i%j;\n"
                +"    //@ show q,m,j*q,j*(q+1),j*(q-1),j*q+m;\n"
                +"    if (i >= 0 && j >= 0) { /*@ assert q >= 0; assert i >= j*q; assert m >= 0 && m < j; assert i == (j*q) + m; */ }\n"
                +"    if (i >= 0 && j < 0) { /*@ assert q <= 0; assert i >= j*q;  assert m >= 0 && m < -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j >= 0) { /*@ assert q <= 0; assert i <= j*q; assert m <= 0 && m < -j; assert i == (j*q) + m; */ }\n"
                +"    if (i < 0 && j < 0) { /*@ assert q >= 0; assert i <= j*q; assert m <= 0 && m > j; assert i == (j*q) + m; */ }\n"
                +"  }\n"
                +"}\n"
              );
    }
    


}

