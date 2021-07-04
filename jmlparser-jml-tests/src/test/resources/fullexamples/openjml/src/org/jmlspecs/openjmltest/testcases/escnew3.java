package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnew3 extends EscBase {

    public escnew3(String options, String solver) {
        super(options,solver);
    }
    
    // Test well-definedness within the implicit old
    @Test
    public void testNonNullElements() {
        Assume.assumeTrue(!"z3_4_3".equals(solver));
        Assume.assumeTrue(!"cvc4".equals(solver));
        Assume.assumeTrue(!"yices2".equals(solver)); // TODO: yices2 cannot handle quantifiers - better error message
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1x(/*@ non_null */ Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assume a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a != null;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m11a(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a);\n"
                +"    //@ assert a == null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(Object[] a) {\n"
                +"    //@ assume a != null && a.length > 1;\n"
                +"    //@ assert a[0] != null;\n"  // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m22(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m3(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    a[0] = new Object();" // No return so as not to bollix the line numbers in the error messages
                +"    //@ assert a[0] != null;\n" // OK
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m33(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 1;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m4(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m44(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 2;\n"
                +"    //@ assume a[0] != null;\n"
                +"    //@ assume a[1] != null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m4a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    a[1] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5(Object[] a) {\n"
                +"    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                +"    a[0] = new Object();\n"
                +"    //@ assert \\nonnullelements(a);\n" // OK
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5a(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n" // Line 75
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                +"  public void m5b(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 3;\n"
                +"    //@ assume \\nonnullelements(a);\n" 
                +"    a[0] = null;\n"
                +"    //@ assert \\nonnullelements(a);\n" // BAD
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5c(Object[] a) {\n"
                +"    //@ assume a != null && a.length == 0;\n"
                +"    //@ assert \\nonnullelements(a);\n"
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a",9
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:65: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                ,"/tt/TestJava.java:77: warning: The prover cannot establish an assertion (Assert) in method m5a",9
                ,"/tt/TestJava.java:84: warning: The prover cannot establish an assertion (Assert) in method m5b",9
                );
    }
    
    @Test
    public void testNotModified() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1a(int i) {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  public int i;\n"
                +"  public static int si;\n"
                +"  //@ ghost public int gi;\n"
                
                +"  //@ requires i == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m2a() {\n"
                +"    i = 5;\n"
                +"    //@ assert \\not_modified(i);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires si == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m3a() {\n"
                +"    si = 5;\n"
                +"    //@ assert \\not_modified(si);\n"  // BAD
                +"  }\n"
                
                +"  //@ requires gi == 5;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m4a() {\n"
                +"    //@ set gi = 5;\n"
                +"    //@ assert \\not_modified(gi);\n"  // BAD
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assert) in method m3a",9
                ,"/tt/TestJava.java:48: warning: The prover cannot establish an assertion (Assert) in method m4a",9
                );
    }
    
    // Test well-definedness within the implicit old
    @Test
    public void testNotModified2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int i;\n"
                +"  public static /*@ nullable */ TestJava t;\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    //@ assert \\not_modified(t.i);\n"  // OK
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1a() {\n"
                +"    t = null;\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                +"  //@ requires t == null;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m1b() {\n"
                +"    t = new TestJava();\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // OK
                +"  }\n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m1c() {\n"
                +"    //@ assert \\not_modified(t.i) ? true: true;\n"  // BAD
                +"  }\n"
                
                 
                +"}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a",31
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b",31
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c",31
                );
    }
    
    @Test
    public void testCast() {
        main.addOptions("-code-math=safe","-spec-math=safe");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static long l;\n"
                +"  public static int i;\n"
                +"  public static short s;\n"
                +"  public static char c;\n"
                +"  public static byte b;\n"
                
                +"  //@ requires i == 6;\n"
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    s = (short)i;\n"
                +"    //@ assert s == i;\n"  // OK
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"  // OK
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
                +"    s = (short)i;\n"  // Line 30
                +"    //@ assert s == i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m0badx() {\n"
                +"    //@ assert i == (short)i;\n" // BAD
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m1badx() {\n"
                +"    //@ assert i == (byte)i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m2badx() {\n"
                +"    //@ assert i == (char)i;\n" 
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m1bad() {\n"
                +"    b = (byte)i;\n"
                +"    //@ assert b == i;\n"
                +"  }\n"
                 
                +"  //@ requires i == 100000;\n"
                +"  //@ modifies \\everything;\n"
                +"  public static void m2bad() {\n"
                +"    c = (char)i;\n"
                +"    //@ assert c == i;\n"
                +"  }\n"
                 
                +"}"
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m0bad",9
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m0badx",21
                ,"/tt/TestJava.java:41: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m1badx",21
                ,"/tt/TestJava.java:46: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m2badx",21
                ,"/tt/TestJava.java:51: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m1bad",9
                ,"/tt/TestJava.java:57: warning: The prover cannot establish an assertion (ArithmeticCastRange) in method m2bad",9
                );
    }
    
    @Test
    public void testCast1() {
        main.addOptions("-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m0() {\n"
                +"    {/*@ nullable */ Short s = null;\n"
                +"    short ss = (short)s;\n"  
                +"    //@ assert 0 == (short)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m1() {\n"
                +"    {/*@ nullable */ Integer s = null;\n"
                +"    int ss = (int)s;\n"  
                +"    //@ assert 0 == (int)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m2() {\n"
                +"    {/*@ nullable */ Long s = null;\n"
                +"    long ss = (long)s;\n"  
                +"    //@ assert 0L == (long)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m3() {\n"
                +"    {/*@ nullable */ Byte s = null;\n"
                +"    byte ss = (byte)s;\n"  
                +"    //@ assert 0 == (byte)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m4() {\n"
                +"    {/*@ nullable */ Character s = null;\n"
                +"    char ss = (char)s;\n"  
                +"    //@ assert 0 == (char)s;\n}"  
                +"  }\n"
                                  
                +"  //@ modifies \\everything;\n"
                +"  public void m7() {\n"
                +"    {/*@ nullable */ Boolean s = null;\n"
                +"    boolean ss = (boolean)s;\n"  
                +"    //@ assert (boolean)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m0",23
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1",19
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m2",21
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m3",21
                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m4",21
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m7",27
                );
    }
    
    @Test
    public void testCast1real() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        main.addOptions("-logic=AUFLIRA","-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m5() {\n"
                +"    {/*@ nullable */ Double s = null;\n"
                +"    double ss = (double)s;\n"  
                +"    //@ assert 0 == (double)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m5",17
                );
    }
    
    @Test
    public void testCast1realb() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        main.addOptions("-logic=AUFLIRA","-escMaxWarnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ modifies \\everything;\n"
                +"  public void m6() {\n"
                +"    {/*@ nullable */ Float s = null;\n"
                +"    float ss = (float)s;\n"  
                +"    //@ assert 0.0 == (float)s;\n}"  
                +"  }\n"
                                  
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m6",16
                );
    }
    
    // TODO - test not_modified and old nested in each other; remember to test definedness            

    @Test
    public void testAssignableConstructor0() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable \\everything;\n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor1() {
        expectedExit = 1;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable i;\n"
                +"  public void mm() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                ,"/tt/TestJava.java:4: An identifier with private visibility may not be used in a assignable clause with public visibility",18
                );
    }

    @Test
    public void testAssignableConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ assignable \\nothing;\n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:5: warning: Associated declaration",10
                );
    }

    @Test
    public void testAssignableConstructor3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ requires true; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor3ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ requires true; pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",22
                );
    }

    @Test
    public void testAssignableConstructor3e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private int i;\n"
                +"  //@ pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assignable) in method TestJava:  i",25
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testAssignableConstructor4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ requires true;\n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ requires true; pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor5() {
    	//main.addOptions("-jmldebug");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ pure \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor5s() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { //@ public nullable model Object state;\n"
                +"  private int i; //@ in state;\n"
                +"  //@ pure \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ requires true; \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor6ae() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava {\n"
                +"  /*@ spec_public */ private int i;\n"
                +"  //@ requires true; pure \n" // default assignable
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor7() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  /*@ spec_public */ private int i; \n"
                +"  //@ pure \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor7s() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  /*@ spec_public */ private int i; \n"
                +"  //@ pure \n"
                +"  public TestJava() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new TestJava(); }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default */ public class TestJava { \n"
                +"  //@ ensures \\result == ints.length;\n"
                +"  //@ pure \n"
                +"  public static int m(Integer ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    return ints.length; }\n"
                
                +"  public static void n(/*@ non_null*/Integer[] args) { \n"
                +"    int i = m(args); \n"
                +"    //@ assert i == args.length; \n"
                +"    }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(1); \n"
                +"    //@ assert i == 1; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(1,1); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ ensures \\result == (ints.length > 0 ? ints[0] : (int)ints.length);\n"
                +"  //@ pure \n"
                +"  public static int m(int ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    if (ints.length > 0) return ints[0]; else return ints.length; }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(2); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(5,6); \n"
                +"    //@ assert i == 5; \n"
                +"    }\n"
                +"}"
                );
    }

    @Test
    public void testVarargs3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires ints.length == 0 || ints[0] != null;\n"
                +"  //@ ensures \\result == (ints.length > 0 ? ints[0] : (int)ints.length);\n"
                +"  //@ pure \n"
                +"  public static int m(Integer ... ints) { \n"
                +"    //@ assert ints != null; \n"
                +"    if (ints.length > 0) return ints[0]; else return ints.length; }\n"
                
                +"  public static void n0() { \n"
                +"    int i = m(); \n"
                +"    //@ assert i == 0; \n"
                +"    }\n"
                
                +"  public static void n1() { \n"
                +"    int i = m(2); \n"
                +"    //@ assert i == 2; \n"
                +"    }\n"
                
                +"  public static void n2() { \n"
                +"    int i = m(5,6); \n"
                +"    //@ assert i == 5; \n"
                +"    }\n"
                +"}"
                );
    }


    @Test
    public void testBits() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {\n"
                +"     boolean b = true;\n"
                +"     boolean bb = false;\n"
                +"     //@ assert !(b & bb);\n"
                +"     //@ assert (b | bb);\n"
                +"     //@ assert (b ^ bb);\n"
                +"     //@ assert (b & bb);\n" // FALSE
                +"    }\n"
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    
    }
    
    @Test
    public void testLabels() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  //@ requires iii == 10;\n"
                + "  public void m(int iii) {\n"
                + "     a:{};\n"
                + "     iii = 12;\n"
                + "     b:{};\n"
                + "     iii = 14;\n"
                + "     //@ assert \\old(iii) == 10;\n"
                + "     //@ assert \\old(iii,a) == 10;\n"
                + "     //@ assert \\old(iii,b) == 12;\n"
                + "     //@ assert iii == 14;\n"
                + "    }\n"
                + "}"
                 );
        
    }

     @Test
    public void testLabels2() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  public int k;\n"
                + "  /*@ ensures \\result == k; pure */ public int mm() { return k; }\n"
                + "  //@ requires k == 10;\n"
                + "  public void m() {\n"
                + "     a:{}\n"
                + "     k = 12;\n"
                + "     b:{}\n"
                + "     k = 14;\n"    // Line 10
                + "     //@ assert \\old(mm()) == 10;\n"
                + "     //@ assert \\old(mm(),a) == 10;\n"
                + "     //@ assert \\old(mm(),b) == 12;\n"
//                + "     //@ assert mm() == 14;\n"
                + "    }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testOldClause() {
    	main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k; requires k == 5 && i > kk && i < 100 && i > -100; assignable k; ensures k == i+1; ensures kk == 5;\n"
                + "  //@ also\n"
                + "  //@ old int kk = k+1; requires k == 5 && i < kk && i < 100 && i > -100; assignable k; ensures k == i-1; ensures kk == 6;\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test // Can reuse labels but not nest them
    public void testLabelScopeBad() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  public int k;\n"
                              + "  public void m() {\n"
                              + "     //@ assert \\old(k,a) == 10;\n"
                              + "     a:{}\n"
                              + "     k = 12;\n"
                              + "     while(k > 10) {  a:{} k--; }\n"
                              + "     while(k > 6) {  b:{ b:{} } k--; }\n"
                              + "     while(k > 5) {  b:{} b:{} k--; }\n"
                              + "     while(k > 0) {  c:{} k--;}\n"
                              + "     k = 14;\n"
                              + "     //@ assert \\old(k,c) == 12;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:5: There is no label named a", 24 
                              ,"/tt/TestJava.java:9: label b already in use", 26
                              );
                      
        
    }

    @Test // Can reuse labels but not nest them
    public void testLabelScope() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  public int k;\n"
                              + "  public void m() {\n"
                              + "     int x = 100;\n"
                              + "     d:{}\n"
                              + "     x = 101;\n"
                              + "     //@ assert 100 == \\old(x,d);\n" // 100
                              + "     d:{}\n"
                              + "     x = 102;\n"
                              + "     //@ assert 101 == \\old(x,d);\n" // 101
                              + "     d:{}\n"
                              + "     x = 103;\n"
                              + "     //@ assert 102 == \\old(x,d);\n" // 102
                              + "    }\n"
                              + "}"
                              );
                      
        
    }

    @Test
    public void testPreconditionOnly() {
        main.addOptions("-checkFeasibility=preconditionOnly");
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     //@ assert i != i;\n" // ERROR
                              + "    }\n"
                              + "\n"
                              + "  //@ requires i > 0;\n"
                              + "  //@ requires i < 0;\n"
                              + "  public void mm(int i) {\n"
                              + "     //@ assert i != i;\n"
                              + "    }\n"
                              + "  //@ requires i > 0;\n"
                              + "  //@ ensures \\result > 0;\n"
                              + "  public int mmm(int i) {\n"
                              + "     return -i;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m",10
                              ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.mm(int)",15
                              ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method mmm",6
                              ,"/tt/TestJava.java:14: warning: Associated declaration",7
                              );
                      
        
    }


    @Test
    public void testIfNoBrace() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        //@ assert i < 0;\n" // OK
                              + "        i = -i; \n"
                              + "     //@ assert i >= 0;\n" // OK
                              + "    }\n"
                              + "}"
                               );
                      
        
    }

    @Test
    public void testIfNoBrace2() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        i = -i; \n"
                              + "        //@ assert i < 0;\n"  // false, since not in if
                              + "     //@ assert i >= 0;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m", 13
                               );
                      
        
    }

    @Test
    public void testIfNoBrace3() {
        helpTCX("tt.TestJava",
                                "package tt; \n"
                              + "public class TestJava { \n"
                              + "  //@ requires i > -10 && i < 10;\n"
                              + "  public void m(int i) {\n"
                              + "     if (i < 0) \n"
                              + "        i = -i; \n"
                              + "        //@ assert i > 0;\n"  // false, since not in if
                              + "     //@ assert i >= 0;\n"
                              + "    }\n"
                              + "}"
                              ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m", 13
                               );
                      
        
    }

    @Test
    public void testOldClause2() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  static public int k = 5;\n"
                + "  //@ old int kk = k;\n"
                + "  //@ {| requires i < 10 && i > kk; assignable k; ensures k == i+1; \n"
                + "  //@ also\n"
                + "  //@    requires i > -10 && i < kk; assignable k; ensures k == i-1; \n"
                + "  //@ |}\n"
                + "  static public void m(int i) {\n"
                + "     if (i>k) k = i+1; else k = i-1;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    

    // Problem from Michael Coblenz - git issue #504
    @Test
    public void testSimpleClone() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  public String y = \"\";\n"
                + " \n"
                + "  public int[] foo() {\n"
                + "     int[] result1 = new int[]{1};\n"
                + "     int[] result2 = result1.clone();\n"
                + "     return result2;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testTriggers() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ ensures \\result == i>=0; \n"
                + "  //@ pure\n"
                + "  public boolean bb(int i) { return i >= 0; }\n"
                + "  public void foo() { int j;\n"
                + "     //@ assert (\\forall int i; 0<=i ; bb(i) : bb(i));\n"
                + "     //@ assert (\\forall int i; 0<=i ; i>=-1 : i>=0, i<=0);\n"
                + "  }\n"
                + "}"
                 );
        
    }
    
    @Test
    public void testTriggersBad() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ pure\n"
                + "  public boolean bb(int i) { return i >= 0; }\n"
                + "  public void foo() { int j;\n"
                + "     //@ assert (\\forall int i; 0<=i ; bb(i) : );\n"
                + "     //@ assert (\\forall boolean i;  ; i : bb(i));\n"
                + "     //@ assert 0 == (\\sum int i; 0<=i ; i : i);\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: incompatible types: boolean cannot be converted to int",47
                ,"/tt/TestJava.java:8: warning: Triggers only recognized in \\forall or \\exists quantified expressions",46
                 );
        
    }
    
    @Test
    public void testExceptionNegativeIndex() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     int j = a[i];\n"  // Old error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { int j = a[i]; } catch (ArrayIndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { int j = a[0]; } catch (ArrayIndexOutOfBoundsException e) {}\n"
                + "     int j = a[i];\n"  // Old Error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { int j = a[i]; } catch (IndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooD(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { int j = a[0]; } catch (NullPointerException e) {}\n"
                + "     int j = a[i];\n" // Old Error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= -1;\n"
                + "  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;\n"
                + "  public void fooE(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     int j = a[i];" // New error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= 0;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooF(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     int j = a[i];" // No error
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",15
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",15
                ,"/tt/TestJava.java:35: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",15
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",15
                ,"/tt/TestJava.java:37: warning: Associated declaration",14
                 );
        
    }
    
    @Test
    public void testExceptionNegativeIndexAssign() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] = 0;\n"  // Old error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}\n"
                + "     a[i] = 0;\n"  // Old Error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] = 0; } catch (IndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooD(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] = 0; } catch (NullPointerException e) {}\n"
                + "     a[i] = 0;\n" // Old Error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= -1;\n"
                + "  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;\n"
                + "  public void fooE(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] = 0;" // New error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= 0;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooF(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] = 0;" // No error
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",7
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",7
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",13
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",7
                ,"/tt/TestJava.java:37: warning: Associated declaration",14
                 );
        
    }
    
    @Test
    public void testExceptionNegativeIndexAssignOp() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] += 0;\n"  // Old error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] += 0; } catch (ArrayIndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] += 0; } catch (ArrayIndexOutOfBoundsException e) {}\n"
                + "     a[i] += 0;\n"  // Old Error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] += 0; } catch (IndexOutOfBoundsException e) {}\n" // No error
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooD(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume 1 < a.length;\n"
                + "     //@ assume i < a.length;\n"
                + "     try { a[i] += 0; } catch (NullPointerException e) {}\n"
                + "     a[i] += 0;\n" // Old Error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= -1;\n"
                + "  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;\n"
                + "  public void fooE(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] += 0;" // New error
                + "  }\n"
                + "  //@ public normal_behavior requires i >= 0;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooF(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i < a.length;\n"
                + "     a[i] += 0;" // No error
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",7
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",7
                ,"/tt/TestJava.java:34: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",13
                ,"/tt/TestJava.java:42: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",7
                ,"/tt/TestJava.java:37: warning: Associated declaration",14
                 );
        
    }
    
    @Test
    public void testExceptionTooLargeIndex() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     int j = a[i];\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     try { int j = a[i]; } catch (ArrayIndexOutOfBoundsException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i <= a.length;\n"
                + "  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     int j = a[i];\n"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i < a.length;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     int j = a[i];\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",15
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:14: warning: Associated declaration",14
                 );
    }
    @Test
    public void testExceptionTooLargeIndexAssign() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     a[i] = 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i <= a.length;\n"
                + "  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     a[i] = 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i < a.length;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     a[i] = 0;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",7
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:14: warning: Associated declaration",14
                 );
    }
    @Test
    public void testExceptionTooLargeIndexAssignOp() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     a[i]+= 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int[] a, int i) { \n"
                + "     //@ assume a != null;\n"
                + "     //@ assume i >= 0;\n"
                + "     try { a[i]+= 0; } catch (ArrayIndexOutOfBoundsException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i <= a.length;\n"
                + "  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;\n"
                + "  public void fooB(int[] a, int i) { \n"
                + "     a[i]+= 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires 0 <= i && i < a.length;\n"
                + "  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;\n"
                + "  public void fooC(int[] a, int i) { \n"
                + "     a[i]+= 0;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",7
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:14: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionDivZero() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int a) { \n"
                + "     int j = 1/a;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int a) { \n"
                + "     try { int j = 1/a; } catch (ArithmeticException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only ArithmeticException;\n"
                + "  public void fooB(int a) { \n"
                + "     int j = 1/a;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != 0;\n"
                + "  //@ also public exceptional_behavior requires a == 0; signals_only ArithmeticException;\n"
                + "  public void fooC(int a) { \n"
                + "     int j = 1/a;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method foo",15
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:11: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionArrayStore() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  Object[] oo = new String[10];  //@ invariant oo.length > 1; \n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int a) { \n"
                + "     oo[0] = 1;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int a) { \n"
                + "     try { oo[0] = 1; } catch (ArrayStoreException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only ArrayStoreException;\n"
                + "  public void fooB(int a) { \n"
                + "     oo[0] = 1;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires \\type(Integer) <: \\elemtype(\\typeof(ooo)) ;\n"
                + "  //@ also public exceptional_behavior requires !(\\type(Integer) <: \\elemtype(\\typeof(ooo))); signals_only ArrayStoreException;\n"
                + "  public void fooC(Object[] ooo, int a) { \n"
                + "     //@ assume ooo.length > 1 ;\n"
                + "     ooo[0] = 1;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method foo",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",12
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionCallNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  /*@ public normal_behavior */ public int m() { return 0; }\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ TestJava a) { \n"
                + "     int j = a.m();\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ TestJava a) { \n"
                + "     try { int j = a.m(); } catch (NullPointerException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ TestJava a) { \n"
                + "     int j = a.m();\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ TestJava a) { \n"
                + "     int j = a.m();\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:11: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionNewNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A {}\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ TestJava a) { \n"
                + "     A j = a.new A();\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ TestJava a) { \n"
                + "     try { A j = a.new A(); } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ TestJava a) { \n"
                + "     A j = a.new A();\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ TestJava a) { \n"
                + "     A j = a.new A();\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",12
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionUnboxNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A {}\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ Integer a) { \n"
                + "     int j = (int)a;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ Integer a) { \n"
                + "     try { int j = (int)a; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ Integer a) { \n"
                + "     int j = (int)a;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ Integer a) { \n"
                + "     int j = (int)a;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method foo",19
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",19
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionUnboxImplicitNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A {}\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ Integer a) { \n"
                + "     int j = a;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ Integer a) { \n"
                + "     try { int j = a; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ Integer a) { \n"
                + "     int j = a;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ Integer a) { \n"
                + "     int j = a;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method foo",14
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",14
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionAssignNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A { int x; }\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     a.x = 1;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { a.x = 1; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     a.x = 1;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     a.x = 1;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionAssignOpNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A { int x; }\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     a.x += 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { a.x += 0; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     a.x += 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     a.x += 0;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionSwitchNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  enum A { X,Y; };\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     switch (a) {};\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { switch (a) {}; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     switch (a) {};\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     switch(a) {};\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullValue) in method foo",13
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",13
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionSynchNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A { }\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     synchronized (a) {};\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { synchronized (a) {}; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     synchronized (a) {};\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     synchronized(a) {};\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullValue) in method foo",19
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",19
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionThrowNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  class A extends RuntimeException {}\n"
                + "  //@ public behavior signals_only A;\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     throw a;\n"
                + "  }\n"
                + "  //@ public behavior signals_only A;\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { throw a; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  //@ public behavior signals_only A;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only A, NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     throw a ;\n"
                + "  }\n"
                + "  //@ public behavior requires a != null; signals_only A;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only A, NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     throw a;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullValue) in method foo",12
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (ExceptionList) in method fooB",12
                ,"/tt/TestJava.java:12: warning: Associated declaration",23
                 );
    }
    
    @Test
    public void testExceptionArrayNull() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ int[] a) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     int j = a[0];\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     try { int j = a[0]; } catch (NullPointerException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires i>0;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     int j = a[0];\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     int j = a[0];\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionArrayNullAssign() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ int[] a) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] = 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     try { a[0] = 0; } catch (NullPointerException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires i>0;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] = 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] = 0;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionArrayNullAssignOp() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ int[] a) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] += 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     try { a[0] = 0; } catch (NullPointerException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires i>0;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] = 0;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ int[] a, int i) { \n"
                + "     //@ assume a != null ==> a.length > 1;\n"
                + "     a[0] = 0;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testExceptionDeref() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  public static class A { public int x; }\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(/*@ nullable */ A a) { \n"
                + "     int j = a.x;\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(/*@ nullable */ A a) { \n"
                + "     try { int j = a.x; } catch (NullPointerException e) {}\n"
                + "  }\n"
                + "  public void fooAA(/*@ nullable */ A a, NullPointerException en) {//@ assume a == null & en != null; \n"
                + "     try { int j = a.x; } catch (NullPointerException e) {/*@ assert a == null; */ }\n"
                + "     int k = a.x;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NullPointerException;\n"
                + "  public void fooB(/*@ nullable */ A a) { \n"
                + "     int j = a.x;\n"
                + "  }\n"
                + "  //@ public normal_behavior requires a != null;\n"
                + "  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;\n"
                + "  public void fooC(/*@ nullable */ A a) { \n"
                + "     int j = a.x;\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method fooAA",15
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:16: warning: Associated declaration",14
                 );
        
    }
    
    @Test
    public void testExceptionNegArraySize() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ public normal_behavior\n"
                + "  public void foo(int n) { \n"
                + "     int[] j = new int[n];\n"
                + "  }\n"
                + "  //@ public normal_behavior\n"
                + "  public void fooA(int n) { \n"
                + "     try { int[] j = new int[n]; } catch (NegativeArraySizeException e) {}"
                + "  }\n"
                + "  //@ public normal_behavior requires true;\n"
                + "  //@ also public exceptional_behavior requires false; signals_only NegativeArraySizeException;\n"
                + "  public void fooB(int n) { \n"
                + "     int[] j = new int[n];\n"
                + "  }\n"
                + "  //@ public normal_behavior requires n >= 0;\n"
                + "  //@ also public exceptional_behavior requires n < 0; signals_only NegativeArraySizeException;\n"
                + "  public void fooC(int n) { \n"
                + "     int[] j = new int[n];\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNegativeSize) in method foo",24
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",24
                ,"/tt/TestJava.java:10: warning: Associated declaration",14
                 );
    }
    
    @Test
    public void testInvariants() {
        helpTCX("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava {\n"
                + "  //@ ensures \\result == (\\lbl BYTES Integer.BYTES);\n"
                + "  public int foo() {\n"
                + "     return 4;\n"
                + "  }\n"
                + "}"
                 );
        
    }
    

}
