package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking.  They compile a test class 
 * using RAC and then execute the resulting program, catching that
 * programs output.  All the tests here have valid JML - they are testing
 * whether the RAC translations work correctly.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racnew3 extends RacBase {

    /** Sets the classpath used for these tests.  The bin in the classpath
     * brings in the currently compiled runtime classes (so we don't have
     * to build jmlruntime.jar)
     */
    String[] ordrac = new String[]{jdk, "-ea", "-classpath","bin"+z+"../OpenJML/bin-runtime"+z+"testdata",null};

    @Override
    public void setUp() throws Exception {
        rac = ordrac;
        jdkrac = false;
        //noCollectDiagnostics = true; print = true;
        super.setUp();
        //main.addOptions("-verboseness",   "4");
        expectedNotes = 0;
    }
    
    /** Tests not_modified */
    @Test public void testNotModified1() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    public static void main(String... args) {\n" +
                "       m(3);\n" +
                "    }" +
                "    public static void m(int i) {\n" +
                "       i = 3;\n" +
                "       //@ assert \\not_modified(i);\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(i);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:9: JML assertion is false"
        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified2() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(3,2);\n" +
                "    }" +
                "    public void m(int i, int j) {\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(j,this.f,f);\n" +
                "       f=6;\n" +
                "       //@ assert \\not_modified(this.f);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"

        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified3() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(3,2);\n" +
                "    }" +
                "    public void m(int i, int j) {\n" +
                "       i = 4;\n" +
                "       //@ assert \\not_modified(j,this.f,f);\n" +
                "       f=6;\n" +
                "       //@ assert \\not_modified(f);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"

        );        
    }

    /** Tests not_modified */
    @Test public void testNotModified4() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*;  \n" +
                "public class TestJava { \n" +
                "    int f = 5;\n" +
                "    public static void main(String... args) {\n" +
                "       (new TestJava()).m(new int[]{1,2},7);\n" +
                "    }" +
                "    public void m(int[] a, int j) {\n" +
                "       j = 4;\n" +
                "       //@ assert \\not_modified(a[0]);\n" +
                "       a[0]=10;\n" +
                "       //@ assert \\not_modified(a[0]);\n" + // FAILS
                "    }" +
                "}"
                ,"/tt/TestJava.java:10: JML assertion is false"
        );        
    }

 
    // FIXME - need tests for X.f X.* o.* a[*] a[1..3] a[1..]
    
    @Test
    public void testCast() {
        main.addOptions("-code-math=safe","-spec-math=safe");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static double d;\n"
                +"  public static float f;\n"
                +"  public static long l;\n"
                +"  public static int i;\n"
                +"  public static short s;\n"
                +"  public static char c;\n"
                +"  public static byte b;\n"
                
                +"    public static void main(String... args) {\n" 
                +"       i = 6; m0(); \n" 
                +"       i = 100000; m0bad(); \n" 
                +"    }\n" 
                
                +"  //@ requires i == 6;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // OK
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // OK // Line 20
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"  // OK
                +"    l = (long)i;\n"
                +"    //@ assert l == i;\n"  // OK
                +"    int ii = (int)i;\n"
                +"    //@ assert ii == i;\n"  // OK

                +"    //@ assert i == (short)i;\n"
                +"    //@ assert i == (long)i;\n"
                +"    //@ assert i == (char)i;\n"
                +"    //@ assert i == (byte)i;\n"
                +"    //@ assert i == (int)i;\n"
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0bad() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // BAD // Line 37
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // BAD
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"  // BAD
                +"    l = (long)i;\n"
                +"    //@ assert l == i;\n"  // OK
                +"    int ii = (int)i;\n"
                +"    //@ assert ii == i;\n"  // OK

                +"    //@ assert i == (short)i;\n" // BAD // Line
                +"    //@ assert i == (long)i;\n"
                +"    //@ assert i == (char)i;\n"
                +"    //@ assert i == (byte)i;\n"
                +"    //@ assert i == (int)i;\n"
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:36: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:37: JML assertion is false"
                ,"/tt/TestJava.java:38: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:39: JML assertion is false"
                ,"/tt/TestJava.java:40: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:41: JML assertion is false"
                ,"/tt/TestJava.java:46: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:46: JML assertion is false"
                ,"/tt/TestJava.java:48: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:48: JML assertion is false"
                ,"/tt/TestJava.java:49: JML argument to numeric cast is out of range of the target type"
                ,"/tt/TestJava.java:49: JML assertion is false"
                );
    }
    

    @Test
    public void testCast1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m0(); \n" 
                +"    }\n" 
                
                +"  public static void m0() {\n"
                +"    {/*@ nullable */ Short s = null;\n"
                +"    try { //@ assert 0 == (short)s; \n} catch (NullPointerException e) {}\n" 
                +"    try { short d = (Short)null; \n} catch (NullPointerException e) {}\n"  // Lines 10-11
                +"    }\n"
                +"    {/*@ nullable */ Long s = null;\n"
                +"    try { //@ assert 0 == (long)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { long d = (Long)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Byte s = null;\n"
                +"    try { //@ assert 0 == (byte)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { byte d = (Byte)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Integer s = null;\n"
                +"    try { //@ assert 0 == (int)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { int d = (Integer)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Character s = null;\n"
                +"    try { //@ assert 0 == (char)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { char d = (Character)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Float s = null;\n"
                +"    try { //@ assert 0 == (float)s;\n} catch (NullPointerException e) {}\n" 
                +"    try { float d = (Float)null;}\n catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Double s = null;\n"
                +"    try { //@ assert 0 == (double)s;\n} catch (NullPointerException e) {}\n"
                +"    try { double d = (Double)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                +"    {/*@ nullable */ Boolean s = null;\n"
                +"    try { //@ assert (boolean)s;\n} catch (NullPointerException e) {}\n"
                +"    try { boolean d = (Boolean)null;\n} catch (NullPointerException e) {}\n"
                +"    }\n"
                
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:8: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:10: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:14: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:16: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:20: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:22: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:26: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:28: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:32: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:34: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:38: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:40: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:44: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:46: JML Attempt to unbox a null object"
                ,"/tt/TestJava.java:50: JML Attempt to unbox a null object within a JML expression"
                ,"/tt/TestJava.java:52: JML Attempt to unbox a null object"
                );
    }
    

    @Test
    public void testCast2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m1(); \n" 
                +"    }\n" 
                
                +"  public static void m1() {\n"
                +"    short s = (short)9;\n"
                +"    //@ assert 9 == (Short)s;\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    @Test
    public void testVarargs() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"    public static void main(String... args) {\n" 
                +"       m1(args); \n" 
                +"       m1(); \n" 
                +"       m1(\"a\"); \n" 
                +"       m1(\"a\",\"b\"); \n" 
                +"    }\n" 
                
                +"  //@ requires args.length >= 0; \n"
                +"  //@ ensures args.length == \\result; \n"
                +"  public static int m1(String ... args) {\n"
                +"    return args.length;\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    @Test
    public void testTryResources1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
				+"}"
                );

    }
    
    // If RR() throws an exception, flag == 0
    // If close exits normally, flag == 1
    // If close throws an exception, flag == 10
    @Test public void testTryResources1x() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ pure */ public RR(){}\n"
                +"       //@ also assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 10;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    } catch (Exception eee) { \n"
                +"    //@ assert (\\lbl FLAG TestJava.flag) == 0 || TestJava.flag == 1|| TestJava.flag == 10;\n"
                +"    }\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"    //@ assert TestJava.flag == 100;\n" // ERROR - line 19
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }
    
    // Checks that close calls execute in reverse order
    @Test public void testTryResources2() {
    	main.addOptions("-racCheckAssumptions");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"    //@ assert TestJava.flag == 200;\n" // ERROR - line 25
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:25: JML assertion is false"
                );
    }
    
    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2b() {
    	main.addOptions("-racCheckAssumptions");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
        		+"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
        		+"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
        		+"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm(boolean b) {\n"  // Line 26
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b) try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 111;\n" // not feasible - so not checked in RAC
                +"    } catch (EE e) {\n"
                +"      //@ assert TestJava.flag == 1;\n" 
                +"       //@ assert e instanceof EE3 ;\n" // Line 37
                +"      //@ assert TestJava.flag == 100;\n" 
                +"    }\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm(true);\n" 
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:38: JML assertion is false"
                );
    }
    
    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2c() {
    	main.addOptions("-racCheckAssumptions");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"    public static class EE extends RuntimeException {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
        		+"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
        		+"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
        		+"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm(boolean b) {\n"  // Line 26
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b) try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 222;\n" // not feasible - so not checked in RAC
                +"    } catch (EE1 | EE2 | EE3 e) {\n"
                +"       //@ assert e instanceof EE3 ;\n" // Line 36
                +"       //@ assert flag == 2;\n"
                +"       //@ assert flag == 100;\n" // Error
                +"    }\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm(true);\n" 
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:38: JML assertion is false"
                );
    }
    
    // Checks the class of the resulting exception when close calls throw exceptions, but not the try body
    @Test public void testTryResources2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
        		+"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
        		+"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE1 { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() {}\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE2 { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n" // Line 23
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"  // Line 25
                +"    //@ assert TestJava.flag == 0;  \n"
                +"    try {\n"
                +"      try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 222;\n"  // Not feasible - so not checked in RAC
                +"    } catch (EE e) {\n"
                +"       //@ assert TestJava.flag == 2;\n"  // Line 34 // SHould be OK
                +"       //@ assert e instanceof EE1;\n"  // Line 35 // Should be OK
                +"    }\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    // Check that finally block of try encloses declarations and calls to close
    @Test public void testTryResources3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } finally {\n"
                +"      flag = 2;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    // If RR() throws an exception, then catch block will execute
    @Test public void testTryResources4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    boolean normal = true;\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"      normal = false;"
                +"    }\n"
                +"    //@ assert normal ==> flag == 1;\n"
                +"    //@ assert !normal ==> flag == 2;\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    @Test public void testTryResources4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"  // FIXME - should not be able to skip the catch block
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    @Test public void testTryResources4b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"  // FIXME - should not be able to skip the catch block
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    // No resource - executes the catch block
    @Test public void testTryResources4c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2; \n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }
    
    // Checks that the outer finally block is last to execute
    @Test public void testTryResources5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also assignable TestJava.flag;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public static void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"    } finally {\n"
                +"      flag = 5;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 5;\n"
                +"  }\n"

                +"  public static void main(String ... args) {\n"
                +"    mmm();\n" 
                +"  }\n"
                 
                +"}"
                );
    }

}
