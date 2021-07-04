package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Ignore;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racArithmeticModes extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+z+"$SY";
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness=4");
        expectedNotes = 4;  // FIXME - GET RID OF DEPENDENCE ON STATING THIS NUMBER
        main.addOptions("-jmltesting");
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
    }


    @Test public void testNegJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = -250000; int k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                 "i = Integer.MIN_VALUE;  k = -i; System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"true END"
                );
        
    }

    @Test public void testNegJavaLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = -250000; long k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                 "i = Long.MIN_VALUE;  k = -i; System.out.println((k==i) +  \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"true END"
                );
        
    }

    @Test public void testNegSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = -250000; int k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                                "i = Integer.MIN_VALUE;  k = -i; \n System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );
        
    }

    @Test public void testNegSafeLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = -250000; long k = -i; System.out.println((k==i) + \" \" + (k+i) + \" END\"); \n" +
                                "i = Long.MIN_VALUE;  k = -i; System.out.println((k==i) + \" END\");} \n" +
                "}"
                ,"false 0 END"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"true END"
                );
        
    }

    @Test public void testNegMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int j = Integer.MAX_VALUE; long k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "int i = Integer.MIN_VALUE; long kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-2147483647 END"
                ,"2147483648 END"
                );
    }

    @Ignore // FIXME - cannot do code in math mode
    @Test public void testNegMath2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int j = Integer.MAX_VALUE; int k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "int i = Integer.MIN_VALUE; int kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-2147483647 END"
                ,"-2147483648 END"
                );
    }

    @Ignore // FIXME - cannot do code in math mode
    @Test public void testNegMathLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "long j = Long.MAX_VALUE; long k = -j; \nSystem.out.println(k + \" END\"); \n" +
                "long i = Long.MIN_VALUE; long kk = -i; \nSystem.out.println(kk + \" END\");} \n" +
                "}"
                ,"-9223372036854775807 END"
                ,"-9223372036854775808 END"
                );
    }

    @Test public void testCompJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }
    @Test public void testCompSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }

    @Test public void testCompMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = ~i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 2147483647"
                );
    }


    @Test public void testSumJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -2"
                );
    }

    @Test public void testSumSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Test public void testSumJavaLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -2"
                );
    }

    @Test public void testSumSafeLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -2"
                );
    }

    @Test public void testSumMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; long k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4294967294"
                );
    }

    // FIXME - still have to sort out how assignments are handled in Math mode
    @Test public void testSumMathCast() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i + i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }

    @Test public void testSumMathArg() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "  int i = Integer.MAX_VALUE; mm(i+i); } \n" +
                "  static void mm(int k) {System.out.println(\"END \" + k);} }"
                ,"/tt/TestJava.java:2: JML argument to numeric cast is out of range of the target type"
                ,"END -2"
                );
    }


    @Test public void testDiffJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -1"
                );
    }

    @Test public void testDiffSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; int k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Test public void testDiffJavaLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i - Long.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END -1"
                );
    }

    @Test public void testDiffSafeLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MAX_VALUE; long k = i - Long.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END -1"
                );
    }

    @Test public void testDiffMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MAX_VALUE; long k = i - Integer.MIN_VALUE; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4294967295"
                );
    }
 
    @Test public void testDivJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testDivSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; int k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Test public void testDivJavaLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testDivSafeLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                "long i = Long.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (k==i));} \n" +
                "}"
                ,"/tt/TestJava.java:2: JML result of numeric operation is out of range of the target type"
                ,"END true"
                );
    }

    @Test public void testDivMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                "int i = Integer.MIN_VALUE; long k = i / (-1); System.out.println(\"END \" + (-k==i));} \n" +
                "}"
                ,"END true"
                );
    }

    @Test public void testMultJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"END 605032704"
                );
    }

    @Test public void testMultSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Test public void testMultMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                                "int i = 30000; int k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 70000;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 900000000"
                ,"/tt/TestJava.java:3: JML argument to numeric cast is out of range of the target type"
                ,"END 605032704"
                );
    }

    @Test public void testMultJavaLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeJavaMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"END 6553255926290448384"
                );
    }

    @Test public void testMultSafeLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeSafeMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:3: JML result of numeric operation is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Test public void testMultMathLong() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; @CodeBigintMath public class TestJava { public static void main(String[] args) { \n" +
                                "long i = 2000000000L; long k = i * i; System.out.println(\"END \" + k); \n" +
                                " i = 5000000000L;  k = i * i; System.out.println(\"END \" + k);} \n" +
                "}"
                ,"END 4000000000000000000"
                ,"/tt/TestJava.java:3: JML argument to numeric cast is out of range of the target type"
                ,"END 6553255926290448384"
                );
    }

    @Test
    public void testModJava() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeJavaMath @SpecSafeMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
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
    public void testModSafe() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeSafeMath @SpecSafeMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
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
    public void testModMath() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"@CodeBigintMath @SpecBigintMath public class TestJava { \n"
                +"  public static void main(String... args) {\n"
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

}
