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

import com.sun.tools.javac.util.Options;

// FIXME - these were old tests - are they duplicates? should we use them?

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esc extends EscBase {

    // public esc() {
    // super("",isWindows?null:"cvc4");
    // }

    public esc(String options, String solver) {
        super(options, solver);
    }

    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }

    // FIXME = significant failures in boogie

    @Override
    public void setUp() throws Exception {
        // noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written
                                                // this way
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        // main.addOptions("-trace");
        // JmlEsc.escdebug = true;
        // org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        // print = true;
    }

    @Test
    public void testCollect() {
        main.addOptions("-nonnullByDefault", "-method=m");
        helpTCX("tt.TestJava",
                "package tt; \n"
                        + "public class TestJava extends java.io.InputStream implements Comparable<TestJava> { \n"
                        + "  public String m(java.lang.Integer i, Number b) {\n"
                        + "    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n" 
                        + "    return null; \n" // FAILS
                        + "  }\n" + "}\n",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m", 5,
                "/tt/TestJava.java:3: warning: Associated declaration", 17);
    }

    @Test  // version of testCollectB without the calls of getClass and v.add
    public void testCollectA() {
        main.addOptions("-nonnullByDefault", "-method=m"); // Keep these options
        helpTCX("tt.TestJava", "package tt; \n"
                + "public class TestJava extends java.io.InputStream implements Comparable<TestJava> { \n"
                + "  /*@ pure */ public String m(java.lang.Integer i, Number b) {\n"
                + "    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n" 
                + "\n"
                + "    boolean bb = v.elements().hasMoreElements();\n" 
                + "    return null; \n" // FAILS
                + "  }\n" 
                + "}\n",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m", 5,
                "/tt/TestJava.java:3: warning: Associated declaration", 29);
    }

    @Test
    public void testCollectB() {
        main.addOptions("-nonnullByDefault", "-timeout=300");
        helpTCX("tt.TestJava",
                "package tt; \n"
                        + "public class TestJava extends java.io.InputStream implements Comparable<TestJava> { \n"
                        + "  public String m(java.lang.Integer i, Number b) {\n"
                        + "    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n"
                        + "    boolean bb = b instanceof Double;\n" 
                        + "    Object oo = v.getClass();\n"
                        + "    v.add(0,i);\n"
                        + "    bb = v.elements().hasMoreElements();\n" 
                        + "    return null; \n" // FAILS
                        + "  }\n" 
                        + "}\n",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m", 5,
                "/tt/TestJava.java:3: warning: Associated declaration", 17);
    }

    @Test
    public void testCollectC() {
        main.addOptions("-nonnullByDefault", "-timeout=300");
        helpTCX("tt.TestJava",
                "package tt; \n"
                        + "public class TestJava extends java.io.InputStream implements Comparable<TestJava> { \n"
                        + "  public String m(java.lang.Integer i, Number b) {\n"
                        + "    java.util.Vector<Integer> v = new java.util.Vector<Integer>();\n"
                        + "    boolean bb = b instanceof Double;\n" 
                        + "    Object oo = v.getClass();\n"
                        + "    Object o = (Class<?>)v.getClass();\n" 
                        + "    v.add(0,new Integer(0));\n"
                        + "    bb = v.elements().hasMoreElements();\n" 
                        + "    return null; \n" // FAILS
                        + "  }\n" + "}\n",
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m", 5, 
                "/tt/TestJava.java:3: warning: Associated declaration", 17
                );
    }

    // Just testing a binary method
    // It gave trouble because the specs were missing
    @Test
    public void testGen() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  public void m1() {\n" + "    Integer a = Integer.valueOf(0);\n" + "  }\n"

                + "}");
    }

    @Test
    public void testForEachA() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  public void m1() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (Long k: a) {\n"
                + "      //@ assert \\count >= 0;\n" // OK
                + "      //@ assert \\count < a.length;\n" // OK
                + "    }\n" 
                + "  }\n"

                + "  public void m3() {\n" // Line 10
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n" 
                + "      //@ assert \\count >= 1;\n" // BAD
                + "    }\n" 
                + "  }\n"

                + "  public void m4() {\n" 
                + "    long[] a = { 1};\n" 
                + "    long[] b = { 1,2};\n"
                + "    for (long k: a) {\n" 
                + "      //@ ghost int i = \\count;\n" // OK
                + "      //@ assert \\count >= 0;\n" // OK
                + "      for (long kk: b) {\n" 
                + "         //@ assert \\count < 2;\n" // OK
                + "      }\n" 
                + "      //@ assert \\count == i;\n" // OK
                + "    }\n" 
                + "  }\n"

                + "  public void m5() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    long[] b = { 1,2};\n" // Line 30
                + "    for (long k: a) {\n" 
                + "       //@ assert \\count == k-1;\n" // OK
                + "    }\n" 
                + "  }\n"

                + "  public void m6() {\n" 
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\count >= 0 && \\count <= a.length;\n" // OK
                + "    //@ decreases a.length - \\count;\n" // OK
                + "    for (long k: a) {\n" 
                + "    }\n" // Line 40
                + "  }\n"

                + "  public void m6ld() {\n" 
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\count >= 0 && \\count <= a.length;\n" // OK
                + "    //@ loop_decreases a.length - \\count;\n" // OK
                + "    for (long k: a) {\n" 
                + "    }\n" 
                + "  }\n"

                + "  public void m7x() {\n" 
                + "    long[] a = { 1,2,3,4};\n" // Line 50
                + "    //@ decreases a.length - \\count - 2;\n" // -1 on last iteration - BAD
                + "    for (long k: a) {\n" 
                + "    }\n" 
                + "  }\n"

                + "  public TestJava() {}\n" 
                + "}"

                , "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m3", 11
                , "/tt/TestJava.java:51: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method m7x", 9
                );
    }

    @Test
    public void testForEach() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  public void m7y() {\n" 
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ decreases a.length - \\count -2;\n" // BAD - last time through
                + "    for (long k: a) {\n" 
                + "    }\n" + "  }\n"

                + "  public void m7a() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    //@ decreases \\count+10;\n" // BAD - loop does not decrease variant
                + "    for (long k: a) {\n" 
                + "    }\n" 
                + "  }\n"

                + "  public void m8() {\n" 
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\count > 0 && \\count <= a.length;\n" // BAD - first time through loop
                + "    for (long k: a) {\n" 
                + "    }\n" 
                + "  }\n"

                + "  public void m9() {\n" 
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\count >= 0 && \\count < a.length;\n" // BAD - laswt time through loop
                + "    for (long k: a) {\n" 
                + "    }\n" 
                + "  }\n"

                + "  public void m2() {\n" 
                + "    long[] a = { 1L,2L,3L };\n" 
                + "    for (Long k: a) {\n"
                + "      //@ assert \\count >= 0;\n" // OK
                + "      //@ assert \\count < a.length;\n" // OK
                + "    }\n" 
                + "  }\n"

                + "  public void m10() {\n" 
                + "    long[] a = { 1,2 };\n" 
                + "    long[] b = { 1,2};\n"
                + "    for (long k: a) {\n" 
                + "      //@ ghost int i = \\count;\n" // OK
                + "      //@ assert \\count >= 0;\n" // OK
                + "      for (long kk: b) {\n" 
                + "         //@ assert \\count < 2;\n" // OK
                + "      }\n" 
                + "      //@ assert \\count == i;\n" // OK
                + "    }\n" 
                + "  }\n"

                + "  public void m2a() {\n" 
                + "    long[] a = {  };\n" 
                + "    for (Long k: a) {\n"
                + "      //@ reachable;\n" // knows that the loop is not
                                                // executed, so this assert is
                                                // infeasible
                + "    }\n" 
                + "  }\n"

                + "  public TestJava() {}\n" 
                + "}"

                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method m7y",9
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (LoopDecreases) in method m7a",9
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method m8",9
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (LoopInvariant) in method m9",9
                ,"/tt/TestJava.java:49: warning: There is no feasible path to program point at reachable statement in method tt.TestJava.m2a()",11
                );
    }

    @Test
    @Ignore // Needs more builtin invariants to help the prover along and definition of \values
    public void testForEach3() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  public void m1() {\n" 
                + "    Integer[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\values.size() == \\count;\n" 
                + "    for (Integer k: a) {\n" 
                + "    }\n"
                + "  }\n"

                + "  public void m2() {\n" 
                + "    Integer[] a = { 1,2,3,4};\n"
                + "    //@ loop_invariant \\values.size() == \\count;\n" 
                + "    for (Integer k: a) {\n"
                + "      //@ assert \\values.size() == \\count;\n" 
                + "    }\n" 
                + "  }\n"

                + "  public void m3() {\n" 
                + "    Integer[] a = { 1,2,3,4};\n" 
                + "    for (Integer k: a) {\n"
                + "      //@ assert \\values.size() == \\count;\n" 
                + "    }\n" 
                + "  }\n"

                + "  public TestJava() {}\n"

                + "  public void m3a() {\n" // Line 23
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n" 
                + "      //@ assert \\count >= 1;\n" // BAD
                + "    }\n" + "  }\n"

                + "}"

                , "/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assert) in method m3a", 11);
    }

    @Test
    public void testForEach2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n" + "  public void m2() {\n"
                + "    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null; \n"
                + "    Iterator<Integer> it = a.iterator(); //@ assume it != null; \n"
                + "    for (; it.hasNext();  ) {\n" + "        it.next(); \n" + "    }\n" + "  }\n"

                + "  //@ public normal_behavior  ensures true;\n" + "  public void m2bad() {\n"
                + "    Set<Integer> a = new HashSet<Integer>(); //@ assume a != null; \n"
                + "    Iterator<Integer> it = a.iterator(); //@ assume it != null; \n"
                + "    for (; it.hasNext();  ) {\n" + "        it.next(); \n" + "        it.next(); \n" + "    }\n"
                + "  }\n"

                + "  public TestJava() {}"

                + "}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad", 16
                ,"/tt/TestJava.java:11: warning: Associated declaration", 14
                );
    }

    public void testForEach2a1() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"
                + "  //@ public normal_behavior  ensures true;\n" 
                + "  public void m1() {\n"
                + "    Set<Map.Entry<String,String>> a = new HashSet<Map.Entry<String,String>>();\n"
                + "    for (Map.Entry<String,String> k: a) {\n" 
                + "    }\n" 
                + "  }\n"


                + "  public TestJava() {}"

                + "}"

        );
    }

    @Test
    public void testForEach2a2() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n" 
                + "  public void m2() {\n" // Line 10
                + "    List<Map.Entry<String,String>> values = new LinkedList<Map.Entry<String,String>>(); //@ assume values != null; set values.containsNull = true; \n"
                + "    Set<Map.Entry<String,String>> a = new HashSet<Map.Entry<String,String>>(); //@ assume a != null; \n"
                + "    Iterator<Map.Entry<String,String>> it = a.iterator(); //@ assume it != null; \n"
                + "    Map.Entry<String,String> k; \n"
                + "    //@ ghost List<Map.Entry<String,String>> v = values;\n"
                + "    //@ loop_invariant values == v; \n"
                + "    for (; it.hasNext(); values.add(k) ) {\n"  // FIXME - why need k ! null below since implied by second conjunct
                + "        k = it.next();  //@ assume k != null && \\typeof(k) <: \\type(Map.Entry<String,String>); \n" 
                        // FIXME - problems if we have erased type names
                + "    }\n" 
                + "  }\n"


                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEach2a2a() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n" 
                + "  public void m2a() {\n" // Line 26
                + "    List<Map.Entry<String,String>> values = new LinkedList<Map.Entry<String,String>>(); //@ assume values != null; set values.containsNull = true; \n"
                + "    Set<Map.Entry<String,String>> a = new HashSet<Map.Entry<String,String>>(); //@ assume a != null; \n"
                + "    Iterator<Map.Entry<String,String>> it = a.iterator(); //@ assume it != null; \n"
                + "    Map.Entry<String,String> k;\n"
                + "    //@ ghost List<Map.Entry<String,String>> v = values;\n"
                + "    // @ loop_invariant values == v; \n"
                + "    if (it.hasNext()) {\n" 
                + "        k = it.next();  //@ assume k != null &&  \\typeof(k) <: \\type(Map.Entry<String,String>); \n" 
                                // FIXME - problems if we have erased type names
                + "        values.add(k); \n"
                                // FIXME - problems if we have erased type names
                + "    }\n" 
                + "  }\n"

                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEach2a3() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n" 
                + "  public void m3() {\n" 
                + "    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true; \n"
                + "    Integer k = new Integer(1);\n"
                + "    values.add(k);\n" 
                + "  }\n"

                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEach2a4() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n"
                + "  public void m4() {\n"
                + "    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true; \n"
                + "    Integer k = 0;\n" 
                + "    values.add(k);\n" 
                + "  }\n"

                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEachBad() {
        expectedExit = 1;
        helpTCX("tt.TestJava", 
                  "package tt; \n" 
                + "public class TestJava { \n"

                + "  public void m1a() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n" 
                + "    }\n"
                + "    //@ ghost int i = \\count;\n" // Out of scope
                + "  }\n"

                + "  public void m2() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    //@ ghost int i = \\count;\n" // Out of scope
                + "  }\n"

                + "  public void m4() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n"
                + "      //@ set \\count = 6;\n" // Syntax error
                + "    }\n" + "  }\n"

                + "  public void v1a() {\n" + "    Integer[] a = { 1,2,3,4};\n" + "    for (Integer k: a) {\n"
                + "    }\n" + "    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // Out
                                                                                        // of
                                                                                        // scope
                + "  }\n"

                + "  public void v2() {\n" + "    long[] a = { 1,2,3,4};\n"
                + "    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // Out
                                                                            // of
                                                                            // scope
                + "  }\n"

                + "  public void v4() {\n" + "    Integer[] a = { 1,2,3,4};\n" + "    for (Integer k: a) {\n"
                + "      //@ set \\values = null;\n" // Syntax error
                + "    }\n" + "  }\n"

                + "  public void v10a() {\n" + "    long[] a = { 1,2,3,4};\n" + "    for (long k: a) {\n"
                + "      //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // OK
                + "    }\n" + "  }\n"

                + "}"

                , "/tt/TestJava.java:7: A \\count token is used outside the scope of a foreach loop", 23,
                "/tt/TestJava.java:11: A \\count token is used outside the scope of a foreach loop", 23,
                "/tt/TestJava.java:16: unexpected type\n  required: variable\n  found:    value", 15,
                "/tt/TestJava.java:23: A \\values token is used outside the scope of a foreach loop", 45,
                "/tt/TestJava.java:27: A \\values token is used outside the scope of a foreach loop", 45,
                "/tt/TestJava.java:32: unexpected type\n  required: variable\n  found:    value", 15);
    }

    @Test
    public void testNonNullElements1() {
//        Assume.assumeTrue(runLongTests);
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1x(Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assume a.length > 1;\n"
                + "    //@ assert a[0] != null;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m11(Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assert a != null;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m11a(/*@ non_null */ Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assert a == null;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m11a", 9
                );
    }

    @Test
    public void testNonNullElements2a() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1a(Object[] a) {\n"
                + "    //@ assume a != null && a.length > 1;\n" 
                + "    //@ assert a[0] != null;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1a", 9
                );
    }

    @Test
    public void testNonNullElements2b() {
//      Assume.assumeTrue(runLongTests);
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m2(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 0;\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements2c() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m22(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 0;\n"
                + "    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements3() {
//        Assume.assumeTrue(runLongTests);
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m3(Object[] a) {\n" 
                + "    //@ assume a != null && a.length == 1;\n"
                + "    a[0] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m33(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 1;\n" 
                + "    //@ assume a[0] != null;\n"
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m4(Object[] a) {\n" 
                + "    //@ assume a != null && a.length == 2;\n"
                + "    a[0] = new Object();\n" 
                + "    a[1] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements4() {
//        Assume.assumeTrue(runLongTests);
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"


                + "  //@ modifies \\everything;\n" 
                + "  public void m44(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 2;\n" 
                + "    //@ assume a[0] != null;\n"
                + "    //@ assume a[1] != null;\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m4a(Object[] a) {\n" 
                + "    //@ assume a != null && a.length == 3;\n"
                + "    a[0] = new Object();\n" 
                + "    a[1] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // BAD
                + "  }\n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m5(Object[] a) {\n" 
                + "    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                + "    a[0] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m5a(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 3;\n" 
                + "    a[0] = null;\n"
                + "    //@ assert \\nonnullelements(a);\n" // BAD
                + "  }\n"

                + "}",
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m4a", 9,
                "/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assert) in method m5a", 9);
    }

    @Test
    public void testNotModified() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  //@ requires i == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m1(int i) {\n"
                + "    i = 5;\n" + "    //@ assert \\not_modified(i);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m1a(int i) {\n" + "    i = 5;\n"
                + "    //@ assert \\not_modified(i);\n" // BAD
                + "  }\n"

                + "  public int i;\n" + "  public static int si;\n" + "  //@ ghost public int gi;\n"

                + "  //@ requires i == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m2() {\n"
                + "    i = 5;\n" + "    //@ assert \\not_modified(i);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m2a() {\n" + "    i = 5;\n"
                + "    //@ assert \\not_modified(i);\n" // BAD
                + "  }\n"

                + "  //@ requires si == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m3() {\n"
                + "    si = 5;\n" + "    //@ assert \\not_modified(si);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m3a() {\n" + "    si = 5;\n"
                + "    //@ assert \\not_modified(si);\n" // BAD
                + "  }\n"

                + "  //@ requires gi == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m4() {\n"
                + "    //@ set gi = 5;\n" + "    //@ assert \\not_modified(gi);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m4a() {\n" + "    //@ set gi = 5;\n"
                + "    //@ assert \\not_modified(gi);\n" // BAD
                + "  }\n"

                + "}", "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m1a",
                9, "/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assert) in method m2a", 9,
                "/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Assert) in method m3a", 9,
                "/tt/TestJava.java:48: warning: The prover cannot establish an assertion (Assert) in method m4a", 9);
    }

    // Test well-definedness within the implicit old
    @Test
    public void testNotModified2() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  public int i;\n" 
                + "  public static /*@ nullable */ TestJava t;\n"

                + "  //@ requires t != null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m0() {\n"
                + "    //@ assert \\not_modified(t.i);\n" // OK
                + "  }\n"

                + "  //@ requires t != null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m1a() {\n"
                + "    t = null;\n" 
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // BAD
                + "  }\n"

                + "  //@ requires t == null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m1b() {\n"
                + "    t = new TestJava();\n" 
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1c() {\n"
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a",31
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b",31
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c",31);
    }

    // TODO - test not_modified and old nested in each other; remember to test
    // definedness

    @Test
    public void testFresh() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; \n" + "abstract public class TestJava { \n"

                + "  //@ requires p != null && p != this;\n" 
                + "  //@ modifies \\everything;\n"
                + "  public void m1(Object p) {\n" 
                + "    Object pp = c1(p);\n"   // result is fresh
                + "    //@ assert pp != p;\n" // OK
                + "    //@ assert pp != this;\n" // OK
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m2(Object p) {\n" + "    Object pp = c2(p);\n" + "    //@ assert pp != p;\n" // BAD
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m3(Object p) {\n" + "    Object pp = c2(p);\n" + "    //@ assert pp != this;\n" // BAD
                                                                                                                    // //
                                                                                                                    // Line
                                                                                                                    // 20
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m4(Object p) {\n" + "    Object pp = c1(p);\n" + "    Object q = new Object();\n"
                + "    //@ assert pp != q;\n" // OK
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" 
                + "  //@ modifies \\everything;\n" // Line 30                                                                                                // 30
                + "  public void m5(Object p) {\n" 
                + "    Object pp = c2(p);\n" 
                + "    Object q = new Object();\n"
                + "    //@ assert pp != q;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  //@ ensures \\result != null && \\fresh(\\result);\n"
                + "  //@ ensures \\result != p && \\result != this;\n" + "  public Object m6(Object p) {\n"
                + "    return new Object();\n" // Line 40
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  //@ ensures \\result == null;\n" // BAD
                + "  public Object m6a(Object p) {\n" + "    return new Object();\n" + "  }\n"

                + "  //@ modifies \\everything;\n" + "  //@ ensures \\result != null && \\fresh(\\result);\n"
                + "  //@ ensures \\result == p || \\result == this;\n" // BAD
                + "  public Object m6b(Object p) {\n" + "    return new Object();\n" + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  //@ ensures \\result != null && !\\fresh(\\result);\n" // BAD
                + "  public Object m6c(Object p) {\n" 
                + "    return new Object();\n" 
                + "  }\n"

                + "  Object o;\n" 
                + "  //@ ghost Object oo;\n" 
                + "  static Object so;\n"
                + "  //@ static ghost Object soo;\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m7(Object p) {\n" 
                + "    Object pp = c1(p);\n"
                + "    //@ assert pp != o && pp != oo;\n" // OK
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m7a(Object p) {\n" 
                + "    Object pp = c2(p);\n"
                + "    //@ assert pp != o;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m7b(Object p) {\n" 
                + "    Object pp = c2(p);\n"
                + "    //@ assert pp != oo;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m7c(Object p) {\n" 
                + "    Object pp = c1e(p);\n"  // fresh result
                + "    //@ assert pp != oo;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m7d(Object p) {\n" 
                + "    Object pp = c2e(p);\n"  // not-necessarily fresh result
                + "    //@ assert pp != o;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m8(Object p) {\n" 
                + "    Object pp = c1(p);\n"
                + "    //@ assert pp != so && pp != soo;\n" // OK
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m8a(Object p) {\n" 
                + "    Object pp = c2(p);\n"
                + "    //@ assert pp != so;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m8b(Object p) {\n"
                + "    Object pp = c2(p);\n"
                + "    //@ assert pp != soo;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m8c(Object p) {\n" 
                + "    Object pp = c1e(p);\n" // fresh result
                + "    //@ assert pp != soo;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m8d(Object p) {\n" 
                + "    Object pp = c1e(p);\n" // fresh result
                + "    //@ assert pp != so;\n" // OK
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  public void m9a(Object p) {\n" 
                + "    Object pp = c1n(p);\n" // if pp is allowed to be null, then it might equal o or oo
                + "    //@ assert pp != o && pp != oo;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\nothing;\n" + "  public void m9b(Object p) {\n" + "    Object pp = c1n(p);\n"
                + "    //@ assert pp != so && pp != soo;\n" // BAD
                + "  }\n"

                + "  //@ modifies \\nothing;\n" 
                + "  //@ ensures \\fresh(\\result);\n"
                + "  abstract public Object c1(Object o); \n"

                + "  //@ modifies \\nothing;\n" 
                + "  //@ ensures \\result == null || \\fresh(\\result);\n"
                + "  abstract public Object c1n(Object o); \n"

                + "  //@ modifies \\nothing;\n" 
                + "  //@ ensures true;\n" 
                + "  abstract public Object c2(Object o); \n"

                + "  //@ modifies \\everything;\n" 
                + "  //@ ensures \\result != null && \\fresh(\\result);\n"
                + "  abstract public Object c1e(Object o); \n"

                + "  //@ modifies \\everything;\n" 
                + "  //@ ensures true;\n"
                + "  abstract public Object c2e(Object o); \n"

                + "  public TestJava() {}\n" + "}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method m2", 9,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (Assert) in method m3", 9,
                "/tt/TestJava.java:45: warning: The prover cannot establish an assertion (Postcondition) in method m6a",
                5, "/tt/TestJava.java:43: warning: Associated declaration", 7,
                "/tt/TestJava.java:51: warning: The prover cannot establish an assertion (Postcondition) in method m6b",
                5, "/tt/TestJava.java:49: warning: Associated declaration", 7,
                "/tt/TestJava.java:56: warning: The prover cannot establish an assertion (Postcondition) in method m6c",
                5, "/tt/TestJava.java:54: warning: Associated declaration", 7,
                "/tt/TestJava.java:70: warning: The prover cannot establish an assertion (Assert) in method m7a", 9,
                "/tt/TestJava.java:75: warning: The prover cannot establish an assertion (Assert) in method m7b", 9,
                "/tt/TestJava.java:85: warning: The prover cannot establish an assertion (Assert) in method m7d", 9,
                "/tt/TestJava.java:95: warning: The prover cannot establish an assertion (Assert) in method m8a", 9,
                "/tt/TestJava.java:100: warning: The prover cannot establish an assertion (Assert) in method m8b", 9,
                "/tt/TestJava.java:115: warning: The prover cannot establish an assertion (Assert) in method m9a", 9,
                "/tt/TestJava.java:120: warning: The prover cannot establish an assertion (Assert) in method m9b", 9);
    }

    @Test
    public void testAssignables4a() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public static TestJava p;\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m1() {\n" + "    //@ assume this.k == 0;\n" + "    c1(p);\n" // havoc
                                                                                                // p.*,
                                                                                                // including
                                                                                                // p.k,
                                                                                                // but
                                                                                                // p
                                                                                                // !=
                                                                                                // this
                + "    //@ assert this.k == 0;\n" // OK
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m1a() {\n" + "    //@ assume sk == 0;\n" + "    c1(p);\n" // havoc
                                                                                            // p.*
                                                                                            // does
                                                                                            // not
                                                                                            // include
                                                                                            // sk
                + "    //@ assert sk == 0;\n" // OK
                + "  }\n"

                + "  //@ requires o != null;\n" + "  //@ modifies o.*;\n" + "  public void c1(TestJava o) { } \n"

                + "  //@ requires o != null;\n" + "  //@ modifies TestJava.*;\n" + "  public void c2(TestJava o) { } \n"
                + "}");
    }

    @Test
    public void testAssignables4b() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public static TestJava p;\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m2a() {\n" + "    //@ assume k == 0;\n" + "    c1(this);\n" // havoc
                                                                                                // this.k
                + "    //@ assert k == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m2b() {\n" + "    //@ assume sk == 0;\n" + "    c1(this);\n" // havoc
                                                                                                // this.*,
                                                                                                // not
                                                                                                // static
                                                                                                // fields
                + "    //@ assert sk == 0;\n" // OK
                + "  }\n"

                + "  //@ requires o != null;\n" + "  //@ modifies o.*;\n" + "  public void c1(TestJava o) { } \n"

                + "  //@ requires o != null;\n" + "  //@ modifies TestJava.*;\n" + "  public void c2(TestJava o) { } \n"
                + "}", "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a",
                9);
    }

    @Test
    public void testAssignables4c() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public static TestJava p;\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m3() {\n" + "    //@ assume k == 0;\n" + "    c2(this);\n" // havoc
                                                                                            // TestJava.*
                                                                                            // does
                                                                                            // not
                                                                                            // include
                                                                                            // non-static
                                                                                            // k
                + "    //@ assert k == 0;\n" // OK
                + "  }\n"

                + "  //@ requires p != null && p != this;\n" + "  //@ modifies \\everything;\n"
                + "  public void m3a() {\n" + "    //@ assume sk == 0;\n" + "    c2(this);\n" // havoc
                                                                                                // TestJava.*
                                                                                                // does
                                                                                                // include
                                                                                                // static
                                                                                                // sk
                + "    //@ assert sk == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires o != null;\n" + "  //@ modifies o.*;\n" + "  public void c1(TestJava o) { } \n"

                + "  //@ requires o != null;\n" + "  //@ modifies TestJava.*;\n" + "  public void c2(TestJava o) { } \n"
                + "}", "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m3a",
                9);
    }

    @Test
    public void testAssignables1a() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n" 
                + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1x() {\n" 
                + "    //@ assume k == 0;\n"
                + "    c1(1);\n" 
                + "    //@ assert k == 0;\n" 
                + "  }\n"

                + "  //@ requires i == 0;\n" 
                + "  //@ modifies \\everything;\n"
                + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" 
                + "  public void c1(int i) { } \n" 
                + "}");
    }

    @Test
    public void testAssignables1b() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m1a() {\n" + "    //@ assume k == 0;\n"
                + "    c1(0);\n" + "    //@ assert k == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m1a", 9);
    }

    @Test
    public void testAssignables1c() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m2() {\n" + "    //@ assume sk == 0;\n"
                + "    c1(1);\n" + "    //@ assert sk == 0;\n" + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables1d() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m2a() {\n" + "    //@ assume sk == 0;\n"
                + "    c1(0);\n" + "    //@ assert sk == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testAssignables6a() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; static public int[] sa;\n"

                + "  //@ requires a != null && a.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m3() {\n" + "    //@ assume a[0] == 0;\n" + "    c1(1);\n"
                + "    //@ assert a[0] == 0;\n" + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables6b() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; public static int[] sa;\n"

                + "  //@ requires a != null && a.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m3a() {\n" + "    //@ assume a[0] == 0;\n" + "    c1(0);\n" // modifies
                                                                                                // everything
                + "    //@ assert a[0] == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                anyorder(
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3a",
                                17),
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m3a",
                                17),
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m3a",
                                9))

        );
    }

    @Test
    public void testAssignables6c() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; public static int[] sa;\n"

                + "  //@ requires sa != null && sa.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m4() {\n" + "    //@ assume sa[0] == 0;\n" + "    c1(1);\n"
                + "    //@ assert sa[0] == 0;\n" + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables6d() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; public static int[] sa;\n"

                + "  //@ requires sa != null && sa.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m4a() {\n" + "    //@ assume sa[0] == 0;\n" + "    c1(0);\n"
                + "    //@ assert sa[0] == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}"
        // Should be just three messages, but in an arbitrary order
                ,
                anyorder(
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m4a",
                                18),
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m4a",
                                18),
                        seq("/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m4a",
                                9)));
    }

    @Test
    public void testAssignables5a() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; public static int[] sa;\n"

                + "  //@ requires sa != null && sa.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m5() {\n" + "    //@ assume a == \\old(a);\n" + "    c1(1);\n"
                + "    //@ assert a == \\old(a);\n" + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables5b() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public int k; public static int sk;\n" + "  public int[] a; public static int[] sa;\n"

                + "  //@ requires sa != null && sa.length > 10;\n" + "  //@ modifies \\everything;\n"
                + "  public void m5a() {\n" + "    //@ assume a == \\old(a);\n" + "    c1(0);\n"
                + "    //@ assert a == \\old(a);\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m5a", 9);
    }

    @Test
    public void testAssignables5c() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m6(/*@ non_null*/TestJava t) {\n"
                + "    //@ assume t.k == 0;\n" + "    c1(1);\n" + "    //@ assert t.k == 0;\n" + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables5d() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m6a(/*@ non_null*/TestJava t) {\n"
                + "    //@ assume t.k == 0;\n" + "    c1(0);\n" + "    //@ assert t.k == 0;\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m6a", 9);
    }

    @Test
    public void testAssignables5e() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m7() {\n" + "    c1(1);\n"
                + "    //@ assert sk == \\old(sk);\n" // Should be OK
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}");
    }

    @Test
    public void testAssignables5f() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int k; static int sk;\n"
                + "  int[] a; static int[] sa;\n"

                + "  //@ modifies \\everything;\n" + "  public void m7a() {\n" + "    c1(0);\n"
                + "    //@ assert sk == \\old(sk);\n" // FAILS
                + "  }\n"

                + "  //@ requires i == 0;\n" + "  //@ modifies \\everything;\n" + "  //@ also requires i > 0;\n"
                + "  //@ modifies \\nothing;\n" + "  public void c1(int i) { } \n" + "}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m7a", 9);
    }

    @Test
    public void testAssignables2a() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public int k;\n" + "  public static int sk;\n"

                        + "  //@ modifies k,sk;\n" 
                        + "  public void m1() {\n" 
                        + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c1(0);\n" 
                        + "    //@ assert sk == 0;\n" 
                        + "  }\n"

                        + "  //@ modifies k,sk;\n" 
                        + "  public void m1a() {\n" 
                        + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c1(1);\n" 
                        + "    //@ assert sk == 0;\n" // FAILS
                        + "  }\n"

                        + "  //@ modifies k,sk;\n" 
                        + "  public void m2() {\n" 
                        + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c1(1);\n" 
                        + "    //@ assert k == 0;\n" + "  }\n"

                        + "  //@ modifies k,sk;\n" 
                        + "  public void m2a() {\n" 
                        + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c1(0);\n" 
                        + "    //@ assert k == 0;\n" // FAILS
                        + "  }\n"

                        + "  public static int[] a; public int[] b;\n"

                        + "  //@ requires i == 0;\n" 
                        + "  //@ modifies k;\n" 
                        + "  //@ also requires i > 0;\n"
                        + "  //@ modifies sk;\n" 
                        + "  public void c1(int i) { } \n"

                        + "  //@ requires i == 10;\n" 
                        + "  //@ modifies t.k;\n" 
                        + "  //@ also requires i == 0;\n"
                        + "  //@ modifies \\nothing;\n" 
                        + "  public void c2(int i, TestJava t) {}\n"

                        + "  //@ requires a!=null && 0<=i && i<a.length;\n" 
                        + "  //@ modifies a[i];\n"
                        + "  public void c3(int i) {}\n" 
                        + "  //@ requires b!=null && 0<=i && i<b.length;\n"
                        + "  //@ modifies b[i];\n" 
                        + "  public void c4(int i) {}\n" 
                        + "}",
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m1a", 9,
                "/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testAssignables2b() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public int k;\n" + "  public static int sk;\n"

                        + "  //@ modifies k,sk;\n" + "  public void m3() {\n" + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c2(0,this);\n" + "    //@ assert k == 0;\n" + "  }\n"

                        + "  //@ modifies k,sk;\n" + "  public void m3a() {\n" + "    //@ assume k == 0 && sk == 0;\n"
                        + "    c2(10,this);\n" + "    //@ assert k == 0;\n" // FAILS
                        + "  }\n"

                        + "  public static int[] a; public int[] b;\n" + "  //@ requires a != null && a.length == 5;\n"
                        + "  //@ modifies a[0];\n" + "  public void m4() {\n"
                        + "    //@ assume a[0] == 0 && a[1] == 1;\n" + "    c3(0);\n" + "    //@ assert a[1] == 1;\n"
                        + "  }\n"

                        + "  //@ requires a != null && a.length == 5;\n" + "  //@ modifies a[0];\n"
                        + "  public void m4a() {\n" + "    //@ assume a[0] == 0 && a[1] == 1;\n" + "    c3(0);\n"
                        + "    //@ assert a[0] == 0;\n" // FAILS
                        + "  }\n"

                        + "  //@ requires i == 0;\n" + "  //@ modifies k;\n" + "  //@ also requires i > 0;\n"
                        + "  //@ modifies sk;\n" + "  public void c1(int i) { } \n"

                        + "  //@ requires i == 10;\n" + "  //@ modifies t.k;\n" + "  //@ also requires i == 0;\n"
                        + "  //@ modifies \\nothing;\n" + "  public void c2(int i, TestJava t) {}\n"

                        + "  //@ requires a!=null && 0<=i && i<a.length;\n" + "  //@ modifies a[i];\n"
                        + "  public void c3(int i) {}\n" + "  //@ requires b!=null && 0<=i && i<b.length;\n"
                        + "  //@ modifies b[i];\n" + "  public void c4(int i) {}\n" + "}",
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method m3a", 9,
                "/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Assert) in method m4a", 9);
    }

    @Test
    public void testAssignables2c() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava",
                          "package tt; \n" 
                        + "public class TestJava { \n" 
                        + "  public int k;\n" 
                        + "  public static int sk;\n"

                        + "  public static int[] a; public int[] b;\n"

                        + "  //@ requires b != null && b.length == 5;\n" 
                        + "  //@ modifies b[0];\n"
                        + "  public void m5() {\n" 
                        + "    //@ assume b[0] == 0 && b[1] == 1;\n" 
                        + "    c4(0);\n"
                        + "    //@ assert b[1] == 1;\n" 
                        + "  }\n"

                        + "  //@ requires b != null && b.length == 5;\n" 
                        + "  //@ modifies b[0];\n"
                        + "  public void m5a() {\n" 
                        + "    //@ assume b[0] == 0 && b[1] == 1;\n" 
                        + "    c4(0);\n"
                        + "    //@ assert b[0] == 0;\n" // FAILS
                        + "  }\n"

                        + "  //@ requires b != null && b.length == 5;\n" 
                        + "  //@ modifies b[0];\n"
                        + "  public void m6a() {\n" 
                        + "    //@ assume b[0] == 0 && b[1] == 1;\n" 
                        + "    c3(0);\n" // changes a - get a null deference warning
                        + "  }\n"

                        + "  //@ requires a != null && b != null && b.length == 5  && a.length ==5;\n"
                        + "  //@ modifies a[0],b[0];\n" 
                        + "  public void m6() {\n"
                        + "    //@ assume b[0] == 0 && b[1] == 1;\n" 
                        + "    c3(0);\n"  // changes a - now ok
                        + "    //@ assert b[1] == 1;\n" 
                        + "  }\n"

                        + "  //@ requires i == 0;\n" 
                        + "  //@ modifies k;\n" 
                        + "  //@ also requires i > 0;\n"
                        + "  //@ modifies sk;\n" 
                        + "  public void c1(int i) { } \n"

                        + "  //@ requires i == 10;\n" 
                        + "  //@ modifies t.k;\n" 
                        + "  //@ also requires i == 0;\n"
                        + "  //@ modifies \\nothing;\n" 
                        + "  public void c2(int i, TestJava t) {}\n"

                        + "  //@ requires a!=null && 0<=i && i<a.length;\n" 
                        + "  //@ modifies a[i];\n"
                        + "  public void c3(int i) {}\n" 
                        + "  //@ requires b!=null && 0<=i && i<b.length;\n"
                        + "  //@ modifies b[i];\n" 
                        + "  public void c4(int i) {}\n" + "}",
                seq("/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method m5a", 9,
                  anyorder(
                    seq("/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Assignable) in method m6a:  a[i]",7
                      , "/tt/TestJava.java:20: warning: Associated declaration", 7
                      ),
                    seq("/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Precondition) in method m6a",7
                      , "/tt/TestJava.java:45: warning: Associated declaration", 15
                      , oneof(
                         seq("/tt/TestJava.java:43: warning: Precondition conjunct is false: a != null",17)
                        ,seq("/tt/TestJava.java:43: warning: Precondition conjunct is false: i < a.length",36)
                        )
                 ))));
    }

    @Test
    public void testAssignables3a() {
        main.addOptions("-method=m1a");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public static int[] a;  //@ public invariant a != null && a.length == 10;\n"

                + "  /*@ assignable a; */ public TestJava() {\n" 
                + "     a = new int[10];\n" 
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m1() {\n" 
                + "    //@ assume a[0] == 0 && a[2] == 2;\n"
                + "    c1();\n" 
                + "    //@ assert a[0] == 0;\n" 
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m1a() {\n" 
                + "    //@ assume a[0] == 0 && a[2] == 2;\n"
                + "    c1();\n" 
                + "    //@ assert a[2] == 3;\n" // FAILS
                + "  }\n"

                + "  //@ modifies a[2 .. 4];\n" 
                + "  public void c1() { } \n"

                + "  //@ modifies a[*];\n" 
                + "  public void c2() {}\n"

                + "  //@ modifies a[2 .. ];\n" 
                + "  public void c3() {}\n" 
                + "}",
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m1a", 9);
    }

    @Test
    public void testAssignables3b() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"
                + "  public static int[] a;  //@ public invariant a != null && a.length == 10;\n"

                + "  //@ assignable a;\n" 
                + "  public TestJava() {\n" 
                + "     a = new int[10];\n" 
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m2a() {\n" 
                + "    //@ assume a[0] == 0 && a[2] == 2;\n"
                + "    c2();\n" 
                + "    //@ assert a[0] == 0;\n" // FAILS
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m2b() {\n" 
                + "    //@ assume a[0] == 0 && a[2] == 2;\n"
                + "    c2();\n" 
                + "    //@ assert a[2] == 2;\n" // FAILS
                + "  }\n"

                + "  //@ modifies a[2 .. 4];\n" 
                + "  public void c1() { } \n"

                + "  //@ modifies a[*];\n" 
                + "  public void c2() {}\n"

                + "  //@ modifies a[2 .. ];\n" 
                + "  public void c3() {}\n" 
                + "}",
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m2a", 9,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method m2b", 9);
    }

    @Test
    public void testAssignables3c() {
        main.addOptions("-exclude=<init>");
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"
                + "  public static int[] a;  //@ public invariant a != null && a.length == 10;\n"

                + "  //@ assignable a;\n" 
                + "  public TestJava() {\n" 
                + "     a = new int[10];\n" 
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m3() {\n" 
                + "    //@ assume a[0] == 0 && a[2] == 2;\n"
                + "    c3();\n" 
                + "    //@ assert a[0] == 0;\n" 
                + "  }\n"

                + "  //@ modifies a[*];\n" 
                + "  public void m3a() {\n" 
                + "    //@ assume a[0] == 0 && a[9] == 2;\n"
                + "    c3();\n" 
                + "    //@ assert a[9] == 2;\n" // FAILS
                + "  }\n"

                + "  //@ modifies a[2 .. 4];\n" 
                + "  public void c1() { } \n"

                + "  //@ modifies a[*];\n" 
                + "  public void c2() {}\n"

                + "  //@ modifies a[2 .. ];\n" 
                + "  public void c3() {}\n" + "}",
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method m3a", 9);
    }

    @Test
    public void testFinal() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  public static final int fa = 13;\n"
                + "  public static int a = 15;\n"

                + "  //@ modifies \\everything;\n" + "  public void z() {\n" + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m1() {\n" + "    //@ assume a == 15 && fa == 13;\n"
                + "    z();\n" + "    //@ assert fa == 13;\n" // Should be OK
                + "    //@ assert a == 15;\n" // Should fail
                + "  }\n"

                + "}", "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m1",
                9);
    }

    @Test
    public void testFinal2() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  public static final int fsa = 13;\n"
                + "  public final int fa = 15;\n" + "  public final int fb;\n" + "  public int a = 17;\n"

                + "  public TestJava() {\n" + "    //@ assert fsa == 13;\n" // OK
                + "    //@ assert fa == 15;\n" // OK
                + "    fb = 16;\n" + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m1() {\n" + "    //@ assert fsa == 13;\n" // Should
                                                                                                                // be
                                                                                                                // OK
                + "    //@ assert fa == 15;\n" // Should be OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m2() {\n" + "    //@ assert a == 17;\n" // Not
                                                                                                            // necessarily
                                                                                                            // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m3() {\n" + "    //@ assert fb == 16;\n" // Not
                                                                                                                // necessarily
                                                                                                                // OK
                + "  }\n"

                + "}", "/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method m2",
                9, "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method m3", 9);
    }

    @Test
    public void testMethodCallsWithExceptions() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ code_bigint_math*/  public class TestJava { \n" + "  public static int k;\n"
                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures k == 10;\n"
                        + "  //@ signals (Exception e) k<0; signals_only Exception;\n"
                        + "  public void m1(int i) throws RuntimeException {\n" + "    m(i);\n" + "    k = 10;\n"
                        + "  }\n" + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures k == 10;\n"
                        + "  //@ signals (Exception e) k==-11;\n" + "  //@ signals_only Exception;\n"
                        + "  public void m2(int i) {\n" + "    m(1);\n" + "    m(2);\n" + "    k = 10;\n" // Line
                                                                                                            // 20
                        + "  }\n"

                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures k == 10;\n"
                        + "  //@ signals (Exception e) k==-12;\n" + "  //@ signals_only Exception;\n"
                        + "  public void m3(int i) {\n" + "    m(0);\n" + "    m(2);\n" + "    k = 10;\n" + "  }\n"

                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures k == 10;\n"
                        + "  //@ signals (Exception e) k==-13;\n" // FAILS
                        + "  //@ signals_only Exception;\n" + "  public void m3a(int i) {\n" + "    m(0);\n"
                        + "    m(2);\n" // FAILS
                        + "    k = 10;\n" // Line 40
                        + "  }\n"

                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures \\result == 12;\n"
                        + "  //@ signals (Exception e) false;\n" + "  public int m4(int i) {\n"
                        + "    return 10+m(0)+m(0);\n" + "  }\n"

                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" // Line
                                                                                // 50
                        + "  //@ ensures false;\n" + "  //@ signals (Exception e) k == -11;\n"
                        + "  //@ signals_only Exception;\n" + "  public int m5(int i) {\n"
                        + "    return 10+m(1)+m(0);\n" + "  }\n"

                        + "  //@ requires i >= 0;\n" + "  //@ modifies k;\n" + "  //@ ensures false;\n"
                        + "  //@ signals (Exception e) k == -12;\n" // Line 60
                        + "  //@ signals_only Exception;\n" + "  public int m6(int i) {\n"
                        + "    return 10+m(0)+m(2);\n" + "  }\n"

                        + "  //@ requires i == 0;\n" + "  //@ modifies k;\n" + "  //@ ensures k>0 && \\result == i+1;\n"
                        + "  //@ signals (Exception e) false;\n" + "  //@ also \n" + "  //@ requires i > 0;\n" // Line
                                                                                                                // 70
                        + "  //@ modifies k;\n" + "  //@ ensures false;\n" + "  //@ signals (Exception e) k == -10-i;\n"
                        + "  //@ signals_only Exception;\n" + "  public int m(int i) {\n" + "    if (i > 0) {\n"
                        + "      k = -10-i;\n" + "      throw new RuntimeException();\n" + "    }\n" + "    k = 1;\n"
                        + "    return i+1;\n" + "  }\n" + "}",
                "/tt/TestJava.java:39: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",
                6, "/tt/TestJava.java:35: warning: Associated declaration", 7);
    }

    @Test
    public void testStrings() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava",
                "package tt; //@ code_bigint_math \n" + "public class TestJava { \n" 
                        + "  String s;\n" 
                        + "  String ss = \"abcde\";\n"
                        + "  public boolean m(String sss) {\n" 
                        + "    return sss == (\"abcde\");\n" 
                        + "  }\n"
                        + "  public boolean m1(/*@ non_null*/ String sss) {\n" 
                        + "    return sss.equals(\"abcde\");\n"
                        + "  }\n" 
                        + "}");
    }

    @Test
    public void testRequires() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  TestJava() { }\n" + "  public TestJava(int i) {}\n" // static
                                                                                                                            // invariant
                                                                                                                            // is
                                                                                                                            // assumed
                                                                                                                            // true
                                                                                                                            // at
                                                                                                                            // start
                                                                                                                            // of
                                                                                                                            // constructor,
                                                                                                                            // remains
                                                                                                                            // true
                                                                                                                            // at
                                                                                                                            // end
                        + "  //@ requires false;\n" + "  public static boolean bf(boolean bb) { return true; }\n"
                        + "  //@ requires true;\n" + "  public static boolean bt(boolean bb) { return true; }\n"
                        + "  static public boolean b = true;\n" + "  //@ static public invariant b;\n"
                        + "  //@ requires !b;\n" + "  public static boolean bq(boolean bb) { return true; }\n" + "}",
                "/tt/TestJava.java:6: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.bf(boolean)",
                25,
                "/tt/TestJava.java:12: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.bq(boolean)",
                25);
    }

    @Test
    public void testJava() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  public static boolean bstatic;\n"
                + "  public boolean binstance;\n" + "  public boolean binstance2;\n" + "  /*@ non_null */ Object o;\n"
                + "  //@ ghost nullable Object oo;\n" + "  //@ public static invariant bstatic;\n"
                + "  //@ public invariant binstance;\n" + "  //@ public initially binstance2;\n"
                + "  //@ public constraint binstance2 == \\old(binstance2);\n"
                + "  //@ public static constraint bstatic == \\old(bstatic);\n"

                + "  public static void main(/*@ non_null*/ String[] args) {  }\n"

                + "  //@ requires true;\n" + "  //@ ensures \\result;\n"
                + "  public static boolean b(boolean bb) { return true; }\n"

                + "  //@ requires false;\n" + "  //@ ensures true;\n" + "  public static int i(int ii) { return 0; }\n"

                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public Object inst(int ii) { binstance = ii == 0; o = null; /*@ set oo = null;*/ return null; }\n"

                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public /*@ nullable */ Object insx(int ii) { binstance = true;           /*@ set oo = null;*/ return null; }\n"

                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public Object insy(int ii) { binstance = ii == 0;            return null; }\n"

                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public Object insz(int ii) { binstance = ii == 0;            return o; }\n" + "}" // FIXME
                                                                                                        // -
                                                                                                        // use
                                                                                                        // Optional
                                                                                                        // etc.
                ,anyorder(  // FIXME - review this expected output
//                optional("/tt/TestJava.java:2: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",8 // nothing sets bstatic true
//                ,"/tt/TestJava.java:8: warning: Associated declaration", 21
//                ,"/tt/TestJava.java:9: warning: Associated declaration", 14
//                )
//                ,optional("/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Initially) in method TestJava",8 // nothing sets binstance2 true
//                ,"/tt/TestJava.java:10: warning: Associated declaration", 14
//                ),
                seq("/tt/TestJava.java:2: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",8 // nothings sets binstance true
                ,"/tt/TestJava.java:9: warning: Associated declaration", 14
//                ,"/tt/TestJava.java:10: warning: Associated declaration", 14
                )
                ,seq("/tt/TestJava.java:19: warning: Invariants+Preconditions appear to be contradictory in method tt.TestJava.i(int)",21 // precondition is false
                )
                ,seq("/tt/TestJava.java:22: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method inst",55
                )
                ,seq("/tt/TestJava.java:28: warning: The prover cannot establish an assertion (InvariantExit) in method insy",64 // binstance is false
                ,"/tt/TestJava.java:9: warning: Associated declaration", 14
                )
                ,seq("/tt/TestJava.java:31: warning: The prover cannot establish an assertion (InvariantExit) in method insz",64 // binstance is false
                ,"/tt/TestJava.java:9: warning: Associated declaration", 14
                )
                )
                );
    }

    @Test
    public void testAssert() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  //@ requires bb;\n"
                + "  //@ ensures true;\n"
                + "  public static void bassert(boolean bb, boolean b) { /*@ assume b; */ /*@assert false;*/   }\n" // Should
                                                                                                                    // fail
                                                                                                                    // because
                                                                                                                    // of
                                                                                                                    // the
                                                                                                                    // explicit
                                                                                                                    // assert
                                                                                                                    // false
                + "  //@ requires bb;\n" + "  //@ ensures true;\n"
                + "  public static void bassert2(boolean bb, boolean b) { /*@ assume b; */ /*@assert !bb;*/   }\n" // Should
                                                                                                                    // fail
                                                                                                                    // because
                                                                                                                    // of
                                                                                                                    // the
                                                                                                                    // tautologically
                                                                                                                    // false
                                                                                                                    // assert
                + "  //@ requires bb;\n" + "  //@ ensures true;\n"
                + "  public static void bassert3(boolean bb, boolean b) { /*@ assume bb; */ /*@assert b;*/   }\n" // Should
                                                                                                                    // fail
                                                                                                                    // because
                                                                                                                    // of
                                                                                                                    // the
                                                                                                                    // unprovable
                                                                                                                    // assert
                + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bassert", 75,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method bassert2",
                76,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method bassert3",
                77);
    }


    @Test   // FIXME - bassumeCHAIN1 times out 
    public void testAssume() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { public static final int z = 0; \n" 
                + "  //@ requires bb;\n"
                + "  //@ ensures true;\n"
                + "  public static void bassumeBADASSUMP(boolean bb) { /*@assume z==1 ;*/  /*@ assert false; */ }\n" // Should succeed despite the false assert
                + "  //@ requires bbb;\n"
                + "  public static void bifOK(boolean bb,boolean b, boolean bbb) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                + "  //@ requires b;\n"
                + "  public static void bifBAD(boolean bb,boolean b) { /*@assume true;*/ if (bb) { /*@assume !b;*/ /*@ assert !bb; */ }  }\n"
                + "  //@ requires bb;\n"
                + "  //@ ensures true;\n"
                + "  public static void bassumeBADASSUMP2(boolean bb) { int x = 1; /*@assume 0==x ;*/  /*@ assert true; */ }\n" // Should succeed despite the false assert
+"\n" 
                //+ "  public static void bassumeCHAIN1(boolean bb, boolean b) { if (bb) { /*@ assume !bb; assume bb;*/ b = true;  /* @ assert false; */ } }\n"
                + "  public static void bassumeCHAIN2(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } }\n"
                + "  public static void bassumeMULT(boolean bb, boolean b) { if (bb) { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */ } else { /*@assume bb; assume !bb; */ b = true; /* @ assert false; */} }\n"
                + "  public TestJava() {}\n" 
                + "}"
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeBADASSUMP(boolean)",56
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bassumeBADASSUMP(boolean)",77
                ,"/tt/TestJava.java:5: warning: There is no feasible path to program point at program exit in method tt.TestJava.bassumeBADASSUMP(boolean)",22
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method bifOK",113
                ,"/tt/TestJava.java:9: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bifBAD(boolean,boolean)",84
                ,"/tt/TestJava.java:9: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bifBAD(boolean,boolean)",101
                ,"/tt/TestJava.java:12: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeBADASSUMP2(boolean)",68
                ,"/tt/TestJava.java:12: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.bassumeBADASSUMP2(boolean)",89
                ,"/tt/TestJava.java:12: warning: There is no feasible path to program point at program exit in method tt.TestJava.bassumeBADASSUMP2(boolean)",22
                // The following error is required, but can occur before or
                // after the error on the same line
//                ,anyorder(
//                seq("/tt/TestJava.java:13: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN1(boolean,boolean)",87)
//                ,seq("/tt/TestJava.java:13: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN1(boolean,boolean)",75)
//                )
                ,"/tt/TestJava.java:14: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeCHAIN2(boolean,boolean)",85
                // The following error is required, but can occur before or
                // after the error on the same line
                ,anyorder(
                seq("/tt/TestJava.java:15: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",83)
                ,seq("/tt/TestJava.java:15: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",142)
                )
                ,"/tt/TestJava.java:15: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.bassumeMULT(boolean,boolean)",153
                ,"/tt/TestJava.java:15: warning: There is no feasible path to program point at program exit in method tt.TestJava.bassumeMULT(boolean,boolean)",22
                );
    }

    @Ignore // FIXME - rejuvenate dead branch detection some time
    @Test
    public void testDeadBranch() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  //static int ii;\n"
                        + "  public static void bok(boolean b, int i) { if (b) i = 7; else i = 9; }\n"
                        + "  public static void bok2(boolean b, int i, int ii) { if (b) i = 7; else i = 9; if (b) ii = 7; else ii = 9; }\n"
                        + "  public static void bdead(boolean b, int i) { /*@ assume b; */ if (b) i = 7; else i = 9; }\n"
                        + "  public static void bdeadelse(boolean b, int i) { /*@ assume !b; */ if (b) i = 7; else i = 9; }\n"
                        + "}",
                "/tt/TestJava.java:6: warning: else branch apparently never taken in method tt.TestJava.bdead(boolean,int)",
                69,
                "/tt/TestJava.java:7: warning: then branch apparently never taken in method tt.TestJava.bdeadelse(boolean,int)",
                73);
    }

    @Test
    public void testDecl() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n"
                        + "  public static void bok() { int k = 0; /*@ assert k == 0; */ }\n"
                        + "  public static void bfalse() { int k = 0; /*@ assert k != 0; */ }\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bfalse", 48);
    }

    // FIXME - rejuvenate dead branch detection
    @Test
    public void testIncarnations() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n"
                + "  public static void bnotok() { int k = 10; int i = 0; i = 1; i = k; k = 5; k = i+k; /*@ assert i == 10; assert k == 16; */}\n" // We
                                                                                                                                                    // want
                                                                                                                                                    // to
                                                                                                                                                    // be
                                                                                                                                                    // sure
                                                                                                                                                    // it
                                                                                                                                                    // fails
                + "  public static void bifok(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 10; */}\n"
                + "  public static void bifbad(boolean b) { int k = 10; if (b) { k = k+1; if (b) k = k-1; else k = k+1; } else { k=k-1; if (b) k=k-1; else k=k+1; } /*@ assert k == 11; */}\n" // We
                                                                                                                                                                                                // want
                                                                                                                                                                                                // to
                                                                                                                                                                                                // be
                                                                                                                                                                                                // sure
                                                                                                                                                                                                // it
                                                                                                                                                                                                // fails
                + "  public static void bifbad2(boolean b) { int k = 10; if (b) { k = k+1; if (!b) k = k+1; } else { k=k-1; if (b) {k=k-1; b = false; } } /*@ assert k == 11; */}\n" // We
                                                                                                                                                                                        // want
                                                                                                                                                                                        // to
                                                                                                                                                                                        // be
                                                                                                                                                                                        // sure
                                                                                                                                                                                        // it
                                                                                                                                                                                        // fails
                + "}",
                "/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Assert) in method bnotok", 106,
                // The following error is required, but the order is arbitrary
                // "/tt/TestJava.java:4: warning: else branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", -75,
                // "/tt/TestJava.java:4: warning: then branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", 120,
                // "/tt/TestJava.java:4: warning: else branch apparently never
                // taken in method tt.TestJava.bifok(boolean)", -75,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method bifbad", 150,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method bifbad2",
                140);
    }

    @Test
    public void testOldJava() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                 + "/*@ code_java_math*/ public class TestJava { \n" 
                 + "  static public  int i;\n"
                 + "  //@ static public constraint i > \\old(i);\n" 
                 + "  //@ modifies i;\n"
                 + "  //@ ensures true;\n" 
                 + "  public static void bok() { i = i - 1; }\n" 
                 + "}"
                 ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Constraint) in method TestJava",29
                , "/tt/TestJava.java:4: warning: Associated declaration", 21
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method bok", 22
                ,"/tt/TestJava.java:4: warning: Associated declaration", 21
                );
    }

    @Test
    public void testOld2Math() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ code_bigint_math*/ public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ modifies i;\n" + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { i = i + 1; i = i + 1;}\n" + "  //@ modifies i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" + "  public static void bbad() { i = i - 1; }\n" + "}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method bbad",
                22, "/tt/TestJava.java:8: warning: Associated declaration", 7);
    }

    @Test
    public void testOld2() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
                        + "  static public int i;\n"
                        + "  //@ modifies i;\n" 
                        + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { i = i + 1; i = i + 1;}\n" 
                        + "  //@ modifies i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" 
                        + "  public static void bbad() { i = i - 1; }\n" 
                        + "}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method bbad",
                22, "/tt/TestJava.java:8: warning: Associated declaration", 7);
    }

    @Test
    public void testAt() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
                        + "  static public int i;\n"
                        + "  //@ modifies i;\n" 
                        + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { x: i = i + 1; /*@ assert i == i@x + 1 && i == (i+1)@x; */ i = i + 1;}\n" 
                        + "  //@ modifies i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" 
                        + "  public static void bbad() { i = i - 1; /*@ assert i == i@x + 1; */ }\n" 
                        + "  //@ modifies i;\n" 
                        + "  public void bok2() { x: i = i + 1; /*@ assert i == this.i@x + 1; */ i = i + 1;}\n" 
                        + "  //@ requires a.length > 10 && a[0] >= 0;\n" 
                        + "  //@ modifies i;\n" 
                        + "  public static void bok3(int[] a) { x: i = i + 1; /*@ assert a[0]@x > -1; */ i = i + 1;}\n" 
                        + "}"
                ,"/tt/TestJava.java:9: There is no label named x", 60
                );
    }

    @Test
    public void testNewCompares() { // Just checks parsing
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
                        + "  public static void bok1(int i) { /*@ assert i <<< i || true; */ }\n" 
                        + "  public static void bok2(int i) { /*@ assert i <<<= i || true; */ }\n" 
                        + "}"
                );
    }

    @Test
    public void testReturn() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  //@ requires 0<=ii && ii <=3;\n"
                        + "  //@ ensures ii<=0 ==> \\result ==-ii;\n"
                        + "  public static int bok(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                        + "  //@ requires ii > -2147483648;\n" // Not using
                                                                // system specs
                        + "  //@ ensures \\result == -ii;\n"
                        + "  public static int bbad(int ii) { if (ii==1) return -1; else if (ii==2) return -2; else if (ii==3) return -3; return 0; }\n"
                        + "}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method bbad",
                112, "/tt/TestJava.java:7: warning: Associated declaration", 7);
    }

    @Test
    public void testThrow() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n"
                        + "  public static void bok(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i!=0; */ }\n"
                        + "  public static void bbad(int i) { if (i == 0) throw new RuntimeException(); /*@ assert i==0; */ }\n"
                        + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method bbad", 82);
    }

    @Test
    public void testNonNull() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public /*@ non_null */Object inst(int ii) { return null; }\n" + "  //@ requires ii == 10;\n"
                + "  //@ ensures true;\n" + "  public @NonNull Object inst2(int ii) {  return null; }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",
                47, "/tt/TestJava.java:5: warning: Associated declaration", 14,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",
                43, "/tt/TestJava.java:8: warning: Associated declaration", 10);
    }

    @Test
    public void testNonNull2() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public                Object inst(int ii) { return null; }\n" + "  //@ requires ii == 10;\n"
                + "  //@ ensures true;\n" + "  public          Object inst2(int ii) {  return null; }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",
                47, "/tt/TestJava.java:5: warning: Associated declaration", 32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",
                43, "/tt/TestJava.java:8: warning: Associated declaration", 26);
    }

    @Test
    public void testNonNull3() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "@NonNullByDefault public class TestJava { \n"
                        + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                        + "  public                Object inst(int ii) { return null; }\n"
                        + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                        + "  public          Object inst2(int ii) {  return null; }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",
                47, "/tt/TestJava.java:5: warning: Associated declaration", 32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",
                43, "/tt/TestJava.java:8: warning: Associated declaration", 26);
    }

    // FIXME - the non-null return postcondition error message is not very clear
    // (it is actually assigning null to a nonnull return value)

    @Test
    public void testNonNull4() {
        main.addOptions("-nullableByDefault=false");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  //@ requires ii == 10;\n" + "  //@ ensures true;\n"
                + "  public                Object inst(int ii) { return null; }\n" + "  //@ requires ii == 10;\n"
                + "  //@ ensures true;\n" + "  public          Object inst2(int ii) {  return null; }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method inst",
                47, "/tt/TestJava.java:5: warning: Associated declaration", 32,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method inst2",
                43, "/tt/TestJava.java:8: warning: Associated declaration", 26);
    }

    // Tests that a cast is nonnull if the argument is
    @Test
    public void testNonNull5() {
        main.addOptions("-nullableByDefault=false");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public Integer inst() { \n" + "    @NonNull Object o = new Integer(0);\n"
                        + "    @NonNull Integer i = (Integer)o;\n" + "    return i;\n" + "  }\n"
                        + "  public Integer inst1() { \n" + "    @Nullable Object o = new Integer(0);\n"
                        + "    @NonNull Integer i = (Integer)o;\n" + "    return i;\n" + "  }\n"
                        + "  public Integer inst2() { \n" + "    @Nullable Object o = null;\n"
                        + "    @NonNull Integer i = (Integer)o;\n" + "    return i;\n" + "  }\n" + "}\n",
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNullInitialization) in method inst2:  i",
                22);
    }

    @Test
    public void testNonNullParam() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n" + "  \n"
                        + "  public /*@ non_null*/Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }\n"
                        + "  \n"
                        + "  public /*@ non_null*/Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }\n"
                        + "  \n"
                        + "  public /*@ non_null*/Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }\n"
                        + "  \n"
                        + "  public /*@ non_null*/Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }\n"
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",
                88, "/tt/TestJava.java:6: warning: Associated declaration", 14,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                83, "/tt/TestJava.java:10: warning: Associated declaration", 14);
    }

    @Test
    public void testNonNullParamNL() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }\n" + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",
                74, "/tt/TestJava.java:5: warning: Associated declaration", 7,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                69, "/tt/TestJava.java:9: warning: Associated declaration", 7

        );
    }

    @Test
    public void testNonNullParamNL2() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  \n" + "  public Object inst(boolean b, /*@ non_null */Object i, Object ii) { return i; }\n"
                + "  \n" + "  public Object instbad(boolean b, /*@ non_null */Object i, Object ii) { return ii; }\n"
                + "  \n" + "  public Object inst2(boolean b, @NonNull Object i, Object ii) { return i; }\n" + "  \n"
                + "  public Object inst2bad(boolean b, @NonNull Object i, Object ii) { return ii; }\n" + "}"

        );
    }

    @Test
    public void testNonNullParam2() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",
                102, "/tt/TestJava.java:5: warning: Associated declaration", 7,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                97, "/tt/TestJava.java:9: warning: Associated declaration", 7);
    }

    @Test
    public void testNonNullParam3() {
        main.addOptions("-nullableByDefault=false");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "@NonNullByDefault public class TestJava { \n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",
                102, "/tt/TestJava.java:5: warning: Associated declaration", 7,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                97, "/tt/TestJava.java:9: warning: Associated declaration", 7);
    }

    @Test
    public void testNonNullParam4() {
        main.addOptions("-nullableByDefault=false");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst(boolean b,                Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object instbad(boolean b,                Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2(boolean b,          Object i, /*@ nullable*/Object ii) { return i; }\n"
                        + "  //@ ensures \\result != null;\n"
                        + "  public /*@ nullable*/Object inst2bad(boolean b,          Object i, /*@ nullable*/Object ii) { return ii; }\n"
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method instbad",
                102, "/tt/TestJava.java:5: warning: Associated declaration", 7,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method inst2bad",
                97, "/tt/TestJava.java:9: warning: Associated declaration", 7);
    }

    @Test
    public void testMethodCall() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  static public int j;\n" + "  //@ requires i>0;\n" + "  //@ modifies j;\n"
                + "  //@ ensures j == -i;\n" + "  static public void m(int i) { j = -i; }\n" + "  //@ requires i>1; \n"
                + "  //@ modifies j;\n" + "  //@ ensures \\result == -i;\n"
                + "  public int inst(boolean b, int i) { m(i); return j; }\n" + "  //@ modifies j;\n"
                + "  //@ ensures \\result == j;\n" + "  public int instbad(boolean b, int i) { m(i); return j; }\n"
                + "  //@ modifies j;\n" + "  //@ ensures \\result == i;\n"
                + "  public int instbad2(boolean b, int i) { m(1); return j; }\n" + "}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43
                ,"/tt/TestJava.java:7: warning: Associated declaration", 22
                ,"/tt/TestJava.java:4: warning: Precondition conjunct is false: i > 0",17
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",49
                , "/tt/TestJava.java:16: warning: Associated declaration", 7
                );
    }

    @Test
    public void testMethodCall2() { // Had problems with static and non-static
        helpTCX("tt.TestJava", 
                  "package tt; import org.jmlspecs.annotation.*; \n" 
                + "public class TestJava { \n"
                
                + "  public int j;\n" 
                
                + "  //@ requires i>0;\n" 
                + "  //@ modifies j;\n" 
                + "  //@ ensures j == -i;\n"
                + "  public void m(int i) { j = -i; }\n" 
                
                + "  //@ requires i>1; \n" 
                + "  //@ modifies j;\n"
                + "  //@ ensures \\result == -i;\n" 
                + "  public int inst(boolean b, int i) { m(i); return j; }\n"
                
                + "  //@ modifies j;\n" 
                + "  //@ ensures \\result == j;\n"
                + "  public int instbad(boolean b, int i) { m(i); return j; }\n" 
                
                + "  //@ modifies j;\n"
                + "  //@ ensures \\result == i;\n" 
                + "  public int instbad2(boolean b, int i) { m(1); return j; }\n"
                + "}"
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Precondition) in method instbad",43
                , "/tt/TestJava.java:7: warning: Associated declaration",15
                ,"/tt/TestJava.java:4: warning: Precondition conjunct is false: i > 0",17
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",49
                , "/tt/TestJava.java:16: warning: Associated declaration", 7);
    }

    @Test
    public void testMethodCallRet() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "/*@ code_bigint_math*/ public class TestJava { \n"
                        + "  static public int j;\n" 
                        + "  //@ requires i>0;\n" 
                        + "  //@ modifies j;\n"
                        + "  //@ ensures j == i+1 && \\result == j;\n"
                        + "  static public int m(int i) { j = i+1; return j; }\n" 
                        + "  //@ requires i>1; \n"
                        + "  //@ modifies j;\n" 
                        + "  //@ ensures \\result == \\old(i)+1;\n"
                        + "  public int inst(boolean b, int i) { m(i); m(i); m(i); return j; }\n"
                        + "  //@ requires i>1; \n" 
                        + "  //@ modifies j;\n" 
                        + "  //@ ensures \\result == \\old(i)+3;\n"
                        + "  public int inst2(boolean b, int i) { m(m(m(i))); return j; }\n" 
                        + "  //@ requires i>1; \n"
                        + "  //@ modifies j;\n" 
                        + "  //@ ensures \\result == 3*i+4;\n" 
                        + "  //@ ensures j == i + 1;\n"
                        + "  public int inst3(boolean b, int i) { return m(m(i) + m(i)) + m(i); }\n"
                        + "  //@ requires i>1; \n" 
                        + "  //@ modifies j;\n" 
                        + "  //@ ensures \\result == \\old(i);\n"
                        + "  public int instx(boolean b, int i) { m(i); m(i); m(i); return j; }\n"
                        + "  //@ requires i>1; \n" 
                        + "  //@ modifies j;\n" 
                        + "  //@ ensures \\result == \\old(i)+4;\n"
                        + "  public int instx2(boolean b, int i) { m(m(m(i))); return j; }\n" 
                        + "  //@ requires i>1; \n"
                        + "  //@ modifies j;\n" // Line 30
                        + "  //@ ensures \\result == 3*i+4;\n" 
                        + "  //@ ensures j == i + 2;\n"
                        + "  public int instx3(boolean b, int i) { return m(m(i) + m(i)) + m(i); }\n" + "}"
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Postcondition) in method instx",58
                ,"/tt/TestJava.java:23: warning: Associated declaration", 7
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Postcondition) in method instx2",53
                ,"/tt/TestJava.java:27: warning: Associated declaration", 7
                ,"/tt/TestJava.java:33: warning: The prover cannot establish an assertion (Postcondition) in method instx3",41
                ,"/tt/TestJava.java:32: warning: Associated declaration", 7
        );
    }

    @Test // FIXME - problem with maintaining result of j
    public void testMethodCallThis() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "/*@ code_java_math*/ public class TestJava { \n"
                        + "  public static TestJava o;\n" 
                        + "  public static TestJava p;\n"
                        + "  public int j; static public int sj; \n"

                        + "  //@ assignable \\nothing; ensures \\result == j;\n" 
                        + "  public int m() { return j; }\n"

                        + "  //@ modifies j,sj;\n" 
                        + "  //@ ensures \\result == \\old(j);\n"
                        + "  public int nold() { return j; }\n"

                        + "  //@ modifies j,sj;\n" 
                        + "  //@ ensures \\result == j;\n"
                        + "  public int n() { return j; }\n"

                        + "  //@ modifies j,sj;\n" 
                        + "  //@ ensures \\result == sj;\n"
                        + "  public int sn() { return sj; }\n"

                        + "  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;\n"
                        + "  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n" 
                        + "  //@ ensures \\result == 6;\n"
                        + "  public int inst() { return o.m() + p.m() + j; }\n" // Line 20

                        + "  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3 && o!=this && p!= this;\n"
                        + "  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n" 
                        + "  //@ ensures \\result == 6;\n"
                        + "  public int instok() { int jj = j; /*@ assert (\\lbl OJ o.j) + (\\lbl PJ p.j) + (\\lbl JJ j) == 6; */ return o.nold() + p.nold() + jj; }\n"   
                        // o.n and p.n modify o.j and p.j, returned value is before mod

                        + "  //@ requires o!=null && p != null && o.j == 1 && p.j == 2 && j == 3;\n"
                        + "  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n" 
                        + "  //@ ensures \\result == 6;\n"
                        + "  public int instbadx() { return o.n() + p.n() + j; }\n" // returned value is after modification

                        + "  //@ modifies j,sj;\n" + "  //@ ensures \\result == 6;\n"
                        + "  public int instbad() { return n() + j; }\n" // n() modifies this.j

                        + "  //@ requires o!=null && p != null && sj == 3;\n"
                        + "  //@ modifies j,sj,o.j,o.sj,p.j,p.sj;\n" 
                        + "  //@ ensures \\result == 9;\n"
                        + "  public int instbad2() { return o.sn() + p.sn() + sj; }\n" 
                        + "}"
                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Postcondition) in method instbadx",27
                ,"/tt/TestJava.java:27: warning: Associated declaration", 7
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (Postcondition) in method instbad",26
                ,"/tt/TestJava.java:30: warning: Associated declaration", 7
                ,"/tt/TestJava.java:35: warning: The prover cannot establish an assertion (Postcondition) in method instbad2",27
                ,"/tt/TestJava.java:34: warning: Associated declaration", 7
                );
    }

    // TODO need tests for for loops
    // TODO need tests for do loops

    // TODO - more tests needed, and with specs

    @Test
    public void testForeachSpecs() {
        helpTCX("tt.TestJava", 
                  "package tt; import org.jmlspecs.annotation.*; \n" 
                + "public class TestJava { \n"
                + "  //@ requires \\nonnullelements(a);\n"
                + "  public void inst(int[] a) { \n" 
                + "    boolean b = false;\n"
                + "    //@ assume a != null && a.length > 2 && a[1] == 1;\n"
                + "    //@ loop_invariant b == \\exists int k; 0 <= k < \\count; a[k] > 0;\n"
                + "    for(int i: a) if (i > 0) b = true; \n" 
                + "    //@ assert b ==> a[1] > 0;\n" 
                + "  }\n" 
                + "}");
    }

    @Test
    public void testForLoopSpecs() { // FIXME - want error position at the end
                                        // of the statement that is the loop
                                        // body
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                        + "  public void instb() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i; decreases 3-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                        + "  public void instc() { int n = 0; /*@ loop_invariant 0<=i && i<5 && n==i; decreases 5-i; */ for (int i=0; i<5; i++) n++; /*@ assert n == 5; */ }\n"
                        + "  public void instd() { int n = 0; /*@ loop_invariant 0<=i && i<=5 && n==i-1; decreases 5-i; */ for (int i=0; i<5; i++) n++;  }\n"
                        + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                77// 119
                // ,"/tt/TestJava.java:4: warning: Associated declaration",77
                ,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopInvariant) in method instc",
                40// 118
                // ,"/tt/TestJava.java:5: warning: Associated declaration",40
                ,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariantBeforeLoop) in method instd",
                40// 97
        // ,"/tt/TestJava.java:6: warning: Associated declaration",40
        // FIXME - fix references
        );
    }

    @Test
    public void testDoWhileSpecs() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + " public class TestJava { \n"
                        + "  public void inst() { int i = 5; /*@ loop_invariant i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ reachable; */ }\n"
                        + "  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }\n"
                        + "  public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }\n"
                        + "}",
                anyorder(
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                                61),
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreases) in method instb",
                                61),
                        seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",
                                61)));
    }

    @Test
    public void testDoWhileSpecsJava() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "/*@ code_java_math */ public class TestJava { \n"
                        + "  public void inst() { int i = 5; /*@ loop_invariant  i>0; decreases i; */ do { i = i-1; } while (i>0); /*@ assert i == 0; */ }\n"
                        + "  /*@ code_bigint_math */public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i-2; */ do  i = i+1;  while (i>0); /*@ assert i == 0; */ }\n"
                        + "  /*@ code_bigint_math */public void instc() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ do { i = i+1; } while (i>0); /*@ assert i == 0; */ }\n"
                        + "}",
                anyorder(
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",
                                84),
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreases) in method instb",
                                84),
                        seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",
                                84)));
    }

    @Test
    public void testWhileSpecs() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "/*@ code_bigint_math*/ public class TestJava { \n"
                        + "  public void insta() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "  public void instb() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "  public void instc() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }\n"
                        + "  public void instd() { int i = 5; /*@ loop_invariant i<=5 && i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "}"
                ,anyorder(
                seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",69)
                // ,"/tt/TestJava.java:4: warning: Associated declaration",69
                ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopDecreases) in method instc",69)
                // ,"/tt/TestJava.java:5: warning: Associated declaration",69
                ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (LoopInvariant) in method instc",40)
                ,seq("/tt/TestJava.java:6: warning: The prover cannot establish an assertion (LoopInvariant) in method instd",40)
                )
        // ,"/tt/TestJava.java:6: warning: Associated declaration",40
        // FIXME - adjust to have the location + associated declaration
        );
    }

    @Test
    public void testWhileSpecs2() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
              + "public class TestJava { \n"
              + "  public void insta() { int i = 5; /*@ loop_invariant i> 0; decreases i; */ while (--i > 0) { } /*@ assert i == 0; */ }\n"
              + "  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i-- > 0) { } /*@ assert i == -1; */ }\n"
              + "  public void instc() { int i = 5; /*@ loop_invariant i> 1; decreases i; */ while (--i > 1) { } /*@ assert i == 1; */ }\n"
              + "}"
              );
    }

    @Test
    public void testIncDec() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { int i = 5; i++; /*@ assert i == 6; */ }\n"
                        + "  public void inst1b() { int i = 5; i++; /*@ assert i == 5; */ }\n"
                        + "  public void inst2() { int i = 5; i--; /*@ assert i == 4; */ }\n"
                        + "  public void inst2b() { int i = 5; i--; /*@ assert i == 5; */ }\n"
                        + "  public void inst3() { int i = 5; ++i; /*@ assert i == 6; */ }\n"
                        + "  public void inst3b() { int i = 5; ++i; /*@ assert i == 5; */ }\n"
                        + "  public void inst4() { int i = 5; --i; /*@ assert i == 4; */ }\n"
                        + "  public void inst4b() { int i = 5; --i; /*@ assert i == 5; */ }\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b", 46,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b", 46,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b", 46,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",
                46);
    }

    @Test
    public void testIncDec2() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { int i = 5; int j = i++; /*@ assert j == 5; */ }\n"
                        + "  public void inst1b() { int i = 5; int j = i++; /*@ assert j == 6; */ }\n"
                        + "  public void inst2() { int i = 5; int j = i--; /*@ assert j == 5; */ }\n"
                        + "  public void inst2b() { int i = 5; int j = i--; /*@ assert j == 4; */ }\n"
                        + "  public void inst3() { int i = 5; int j = ++i; /*@ assert j == 6; */ }\n"
                        + "  public void inst3b() { int i = 5; int j = ++i; /*@ assert j == 5; */ }\n"
                        + "  public void inst4() { int i = 5; int j = --i; /*@ assert j == 4; */ }\n"
                        + "  public void inst4b() { int i = 5; int j = --i; /*@ assert j == 5; */ }\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b", 54,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2b", 54,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst3b", 54,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst4b",
                54);
    }

    @Test
    public void testAssignOp() {
        Assume.assumeTrue(runLongTests);
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { int i = 5; i+=7; /*@ assert i == 12; */ }\n"
                        + "  public void inst1b() { int i = 5; i+=7; /*@ assert i == 5; */ }\n"
                        + "  public void inst1c() { int i = 5; int j = (i+=7); /*@ assert i == 12 && i == j; */ }\n"
                        + "  public void inst1d() { int i = 5; int j = (i+=7); /*@ assert i == 5; */ }\n"
                        + "  public void inst2() { int i = 5; i-=7; /*@ assert i == -2; */ }\n"
                        + "  public void inst2b() { int i = 5; i-=7; /*@ assert i == 5; */ }\n"
                        + "  public void inst2c() { int i = 5; int j = (i-=7); /*@ assert i == -2 && i == j; */ }\n"
                        + "  public void inst2d() { int i = 5; int j = (i-=7); /*@ assert i == 5; */ }\n"
                        + "  public void inst3() { int i = 5; i*=7; /*@ assert i == 5*7; */ }\n"
                        + "  public void inst3b() { int i = 5; i*=7; /*@ assert i == 5; */ }\n"
                        + "  public void inst3c() { int i = 5; int j = (i*=7); /*@ assert i == 5*7 && i == j; */ }\n"
                        + "  public void inst3d() { int i = 5; int j = (i*=7); /*@ assert i == 5; */ }\n"
                        + "  public void inst4() { int i = 5; i/=7; /*@ assert i == 5/7; */ }\n"
                        + "  public void inst4b() { int i = 5; i/=7; /*@ assert i == 5; */ }\n"
                        + "  public void inst4c() { int i = 5; int j = (i/=7); /*@ assert i == 5/7 && i == j; */ }\n"
                        + "  public void inst4d() { int i = 5; int j = (i/=7); /*@ assert i == 5; */ }\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1b", 47,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1d", 57,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b", 47,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst2d", 57,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst3b", 47,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst3d", 57,
                "/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Assert) in method inst4b", 47,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method inst4d",
                57); // TODO - need %= <<= >>= >>>= &= |= ^=
    }

    @Test
    public void testConditional() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  //@ requires i > -2147483648;\n"
                        + "  public void inst1(int i) { int j = i<0?-i:i; /*@ assert j >= 0; */ }\n"
                        + "  //@ requires i > -2147483648;\n"
                        + "  public void inst1a(int i) { int j = i<0?-i:i; /*@ assert j == -1; */ }\n" + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1a", 53);
    }

    @Test
    public void testLblx() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i>0); */}\n" // no
                                                                                                                    // report
                        + "  public void inst1a(int i) { /*@ assume i > 0; */ /*@ assert (\\lblneg ISN i<0); */}\n" // reported
                        + "  public void inst1b(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblneg ISN2 i>0); */}\n" // no
                                                                                                                        // report
                        + "  public void inst1c(int i) { /*@ assume i > 0; */ /*@ assert (\\lblpos ISP i<0); */}\n" // no
                                                                                                                    // report
                        + "  public void inst1d(int i) { /*@ assume i > 0; */ /*@ assert !(\\lblpos ISP2 i>0); */}\n" // reported
                        + "}",
                "/tt/TestJava.java:4: warning: Label ISN has value false", 72,
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a", 56,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1b", 56,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst1c", 56,
                "/tt/TestJava.java:7: warning: Label ISP2 has value true", 73,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1d", 56);
    }

    @Test
    public void testNewObject() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { Object o = new Object(); Object oo = new Object(); /*@ assert o != oo;*/ }\n"
                        + "  public void inst1a() { Object o = new Object(); Object oo = new Object(); /*@ assert o == oo;*/ }\n"
                        + "  public void inst2() { Object o = new Object(); /*@ assert o != null;*/ }\n"
                        + "  public void inst2a() { Object o = new Object(); /*@ assert o == null;*/ }\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a", 81,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a", 55);
    }

    @Test
    public void testNewArray() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst1() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o != oo;*/ }\n"
                + "  public void inst1a() { Object o = new int[5]; Object oo = new int[5]; /*@ assert o == oo;*/ }\n" // FALSE
                + "  public void inst2() { int[] o = new int[5]; /*@ assert o != null; assert o.length == 5; */ }\n"
                + "  public void inst2a() { int[] o = new int[5]; /*@ assert o.length == 6;*/ }\n" // FALSE
                + "  public void inst3(/*@non_null*/int[] a) { /*@ assert a.length >= 0;*/ }\n"
                + "  public void inst5() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o != oo;*/ }\n"
                + "  public void inst5a() { Object o = new boolean[5]; Object oo = new boolean[5]; /*@ assert o == oo;*/ }\n" // FALSE
                + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst1a", 77,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst2a", 52,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst5a", 85);
    }

    @Test
    public void testNewArrayInit() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst4() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 11;*/ }\n"
                        + "  public void inst4a() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 4; */ }\n"
                        + "  public void inst4b() { int[] o = new int[]{10,11,12}; /*@ assert o.length == 3; assert o[1] == 10;*/ }\n"
                        + "  public void inst6() { int[] o = {10,11,12}; /*@ assert o != null; assert o.length == 3; assert o[1] == 11;*/ }\n"
                        + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst4a", 61,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst4b", 83);
    }

    @Test
    public void testNewArrayInit2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; assert o[1] != null; assert o[1].length == 3; assert o[1][2] == 14; assert o[0] != null; assert o[0].length == 2; assert o[0][1] == 11; */ }\n"
                        + "  public void inst5() { int[][] o = {{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; assert o[1] != null; assert o[1].length == 3; assert o[1][2] == 14; assert o[0] != null; assert o[0].length == 2; assert o[0][1] == 11; */ }\n"
                        + "  public void inst6() { int[][] o = {{10,11},null,{15}}; /*@ assert o.length == 3; assert o[1] == null; assert o[2] != null; assert o[2].length == 1; assert o[2][0] == 15; */ }\n"
                        + "}");
    }

    @Test
    public void testNewArrayMD1() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst0() { Object o = new int[2][3]; o = new int[2][]; o = new int[][] {{2}, {3,4,5}}; int[][] oo = {{1},{2,3}}; /*@ assert oo[0] != oo[1]; */}\n"
                + "  public void inst1() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o != oo;*/ }\n"
                + "  public void inst1a() { Object o = new int[5][3]; Object oo = new int[5][3]; /*@ assert o == oo;*/ }\n" // FALSE
                + "  public void inst2() { int[][] o = new int[5][3]; /*@ assert o.length == 5; assert o[1].length == 3; */ }\n"
                + "  public void inst2a() { int[][] o = new int[5][3]; /*@ assert o.length == 6;*/ }\n" // FALSE
                + "  public void inst2b() { int[][] o = new int[5][3]; /*@ assert o[1].length == 4;*/ }\n" // FALSE
                + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst1a", 83,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a", 57,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst2b", 57);
    }

    @Test
    public void testNewArrayMD2() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst3(/*@non_null*/int[][] a) { /*@ assert a.length >= 0;*/ }\n"
                + "  public void inst4() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 3; */ }\n"
                + "  public void inst4a() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o.length == 2; */ }\n" // FALSE
                + "  public void inst5() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[1][2] == 14; */ }\n"
                + "  public void inst6() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[2].length == 1; */ }\n"
                + "  public void inst7() { int[][] o = new int[][]{{10,11},{12,13,14},{15}}; /*@ assert o[0].length == 2; */ }\n"
                + "  public void inst8() { int[][] o = new int[5][]; /*@ assert o != null; assert o.length == 5; assert o[1] == null; */ }\n"
                + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst4a", 80);
    }

    @Test
    public void testArrays() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst2(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 2; */ }\n" // OK
                + "  public void inst2a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  /*@ assert a[1] == 3; */ }\n" // BAD
                + "  public void inst3(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */ }\n" // OK
                + "  public void inst3a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 4; */ }\n" // BAD
                + "  public void inst4(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 2; */ }\n" // OK
                + "  public void inst4a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[0] == 2; */  a[1] = 3; /*@ assert a[0] == 4; */ }\n" // BAD
                + "  public void inst5(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 4; */}\n" // OK
                + "  public void inst5a(/*@non_null*/int[] a) { /*@assume a.length == 10;*//*@ assume a[1] == 2; */  a[1] = 3; /*@ assert a[1] == 3; */  a[1] = 4; /*@ assert a[1] == 5; */}\n" // BAD
                + "  public void inst6(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                + "  public void inst6a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                + "  public void inst7(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/ b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 7; */}\n" // OK
                + "  public void inst7a(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 10;*/  b[0] = 0; b = a; a[0] = 7; /*@ assert b[0] == 8; */}\n" // BAD
                + "  public void inst8(/*@non_null*/int[] a, /*@non_null*/int[] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = 5; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n" // BAD
                + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a", 103,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst3a", 113,
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method inst4a", 113,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method inst5a",
                149,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method inst6a",
                106,
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method inst7a",
                147);
    }

    @Test
    public void testArraysMD1() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst2(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert a[1][2]; */ }\n" // OK
                + "  public void inst2a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  /*@ assert !a[1][2]; */ }\n" // BAD
                + "  public void inst3(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = false; /*@ assert !a[1][2]; */ }\n" // OK
                + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst2a",
                154);
    }

    @Test
    public void testArraysMD4() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst3a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[1][3]; */ }\n" // BAD
                + "  public void inst3b(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; */  a[1][2] = true ; /*@ assert a[0][2]; */ }\n" // BAD
                                                                                                                                                                                                                        // -
                                                                                                                                                                                                                        // a[0]
                                                                                                                                                                                                                        // might
                                                                                                                                                                                                                        // be
                                                                                                                                                                                                                        // null;
                                                                                                                                                                                                                        // even
                                                                                                                                                                                                                        // if
                                                                                                                                                                                                                        // it
                                                                                                                                                                                                                        // isn't
                                                                                                                                                                                                                        // a[0][2]
                                                                                                                                                                                                                        // is
                                                                                                                                                                                                                        // not
                                                                                                                                                                                                                        // necessarily
                                                                                                                                                                                                                        // true
                + "  public void inst3c(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; */  a[1][2] = false; /*@ assert a[0][2]; */ }\n" // BAD
                + "}",
                "/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Assert) in method inst3a", 171,
                anyorder(
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst3b",
                                171),
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method inst3b",
                                182),
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method inst3b",
                                182)),
                anyorder(
                        seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method inst3c",
                                203),
                        seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst3c",
                                192)));
    }

    @Test
    public void testArraysMD5() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst3d(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; *//*@ assume a[1][2]; assume a[0] != null; assume a[0].length > 5; */  a[1][2] = false; /*@ assert a[0][2]; */ }\n" // BAD
                + "  public void inst4(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert a[0][0]; */ }\n" // OK
                + "  public void inst4a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[0] != null; assume a[1].length == 5; assume a[0].length == 3; *//*@ assume a[0][0]; */  a[1][0] = false; /*@ assert !a[0][0]; */ }\n" // BAD
                + "}",
                "/tt/TestJava.java:3: warning: The prover cannot establish an assertion (Assert) in method inst3d", 216,
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method inst4a",
                217);
    }

    @Test
    public void testArraysMD2() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst5x(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */  a[0] = a[1]; /*@ assert a[0][3] == a[1][3]; */}\n" // OK
                + "  public void inst5a(/*@non_null*/boolean[][] a) { /*@assume a.length == 10; assume a[1] != null; assume a[1].length == 5; */ a[0] = a[1]; /*@ assert a[0][3] != a[1][3]; ; */}\n" // BAD
                + "  public void inst6(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] == b[0]; */}\n" // OK
                + "  public void inst6a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@assume a.length == 10;*/b = a; /*@ assert a[0] != b[0]; */}\n" // BAD
                + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst5a", 144,
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method inst6a",
                118);
    }

    @Test
    public void testArraysMD3() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public void inst7(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/ b[0][0] = true; b = a; a[0][0] = false; /*@ assert !b[0][0]; */}\n" // OK
                + "  public void inst7a(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 10 && b[0] != null && a[0] != null && b[0].length == 5 && a[0].length==6;*/  b[0][0] = true; b = a; a[0][0] = false; /*@ assert b[0][0]; */}\n" // BAD
                + "  public void inst8(/*@non_null*/boolean[][] a, /*@non_null*/boolean[][] b) { /*@ assume b.length == 10 && a.length == 12;*/ b = a; a[0] = null; /*@ assert b != null; assert a != null; assert b.length == 12; assert a.length == 12; */}\n" // OK
                + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method inst7a",
                242);
    }

    @Test
    public void testFields() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*;/*@ nullable_by_default */  \n"
                + "public class TestJava { \n" + "  int f; static int sf;\n" + "  int g; static int sg;\n"
                + "  public static TestJava t;  //@ public static invariant t != null; \n"
                + "  public void inst2(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }\n" // OK
                + "  public void inst2a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }\n" // BAD
                + "  public void inst3(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }\n" // OK
                + "  public void inst3a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }\n" // BAD
                + "  public void inst4(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }\n" // OK
                + "  public void inst4a(/*@non_null*/int[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }\n" // BAD
                + "  public void inst5(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}\n" // OK
                + "  public void inst5a(/*@non_null*/int[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}\n" // BAD
                + "  public void inst6(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f == b.f; */}\n" // OK
                + "  public void inst6a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f != b.f; */}\n" // BAD
                + "  public void inst7(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}\n" // OK
                + "  public void inst7a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}\n" // BAD
                + "  public void inst8(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf == b.sf; */}\n" // OK
                + "  public void inst8a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf != b.sf; */}\n" // BAD
                + "  public void inst9(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}\n" // OK
                + "  public void inst9a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}\n" // BAD
                + "  public void inst10(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}\n" // OK
                + "  public void inst10a(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}\n" // BAD
                + "  public void inst11(/*@non_null*/TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}\n" // OK
                + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst2a", 75,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst3a", 84,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst4a", 84,
                "/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method inst5a",
                118,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method inst6a", 85,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method inst7a",
                103,
                "/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Assert) in method inst8a", 78,
                "/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method inst9a", 88,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method inst10a",
                81);
    }

    @Test
    public void testSwitch() {
        Assume.assumeTrue(runLongTests || !"cvc4".equals(solver));
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  int f; static int sf;\n" + "  int g; static int sg;\n" + "  static TestJava t;\n"
                + "  public void inst1a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j!=0; */ }\n" // OK
                + "  public void inst1b(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j==1; */ }\n" // BAD
                + "  public void inst2(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                + "  public void inst2a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert i==0 ==> j==-1; */ }\n" // BAD
                + "  public void inst3(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                + "  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; break; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                + "  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method inst1b", 148,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method inst2a", 141,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method inst3a",
                170);
    }

    @Test
    public void testTry() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  static public int i;\n" + "  //@ ensures i == 2;\n"
                        + "  public void inst1() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // OK
                        + "  //@ ensures i == 1;\n"
                        + "  public void inst1a() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // BAD
                        + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method inst1a",
                44, "/tt/TestJava.java:6: warning: Associated declaration", 7);
    }

    @Test
    public void testTryWithMethodCall() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava  {\n"
                + "//@ public exceptional_behavior requires b;  signals (Exception e) true; signals (RuntimeException e) true;\n"
                + "//@ also\n" + "//@ public normal_behavior requires !b; ensures true;\n"
                + "public static void ex(boolean b) throws RuntimeException {\n"
                + "    if (b) throw new RuntimeException();\n" + "}\n" + "public static int sk; public int k;\n" + "\n" // Line
                                                                                                                        // 10
                + "//@ requires k < 0;\n" + "//@ ensures true;\n" + "//@ also\n" + "//@ requires k > 0;\n"
                + "//@ ensures \\result == 1;\n" + "public int m1() {\n" + "    int i = 1;\n" + "    try {\n"
                + "        ex(true);\n" + "        i = 1;\n" // Line 20
                + "    } catch (Exception e) {\n" + "        //@ assert e != null;\n" + "        i = 2;\n" + "    }\n"
                + "    return i;\n" + "}\n" + "\n" + "//@ requires k < 0;\n" + "//@ ensures true;\n" + "//@ also\n" // Line
                                                                                                                    // 30
                + "//@ requires k > 0;\n" + "//@ ensures \\result == 1;\n" + "public int m2() {\n" + "    int i = 1;\n"
                + "    try {\n" + "        ex(false);\n" + "        i = 0;\n" + "    } catch (Exception e) {\n"
                + "        //@ assert e != null;\n" + "        i = 1;\n" // Line
                                                                            // 40
                + "    }\n" + "    return i;\n" + "}\n" + "}",
                "/tt/TestJava.java:25: warning: The prover cannot establish an assertion (Postcondition) in method m1",
                5, "/tt/TestJava.java:15: warning: Associated declaration", 5,
                "/tt/TestJava.java:42: warning: The prover cannot establish an assertion (Postcondition) in method m2",
                5, "/tt/TestJava.java:32: warning: Associated declaration", 5);
    }

    @Test
    public void testMisc() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  static public int i;\n" + "  //@ requires i > 0;\n" + "  //@ ensures i > 0;\n"
                        + "  public static void m() { i = i -1; }\n" // OK
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",
                22, "/tt/TestJava.java:5: warning: Associated declaration", 7);
    }

    @Test
    public void testArith() { // TODO - need more arithmetic support
        Assume.assumeTrue(runLongTests);
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public static void m1(int a, int b) { /*@ assert a*2 == a + a; */ }\n"
                // +" public static void m2(int a, int b) { /*@ assert a * b ==
                // a *(b-1) + a; */ }\n"
                + "  public static void m3(int a, int b) { /*@ assert (2*a)/2 == a; */ }\n"
                + "  public static void m4(int a, int b) { /*@ assert a >= 0 ==> (a%3) < 3; */ }\n"
                + "  public static void m5(int a, int b) { /*@ assert a >= 0 ==> (a%3) >= 0; */ }\n"
                // +" public static void m6(int a, int b) { /*@ assert (a >= 0
                // && b > 0) ==> (a%b) >= 0; */ }\n"
                // +" public static void m7(int a, int b) { /*@ assert (a >= 0
                // && b > 0) ==> ((a*b)%b) == 0; */ }\n"
                + "  public static void m8(int a, int b) { /*@ assert (a >= 0 ) ==> ((5*a)%5) == 0; */ }\n" + "}");
    }

    @Test
    public void testPureMethodStatic() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "public class TestJava { \n" 
                + "  //@ requires i < 1000; ensures \\result == i+1;\n"
                + "  //@ pure \n" 
                + "  public static int m(int i) { return i+1; }\n"
                + "  public static void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }\n"
                + "  public static void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }\n"
                + "  public static void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                + "  public static void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                + "  public static void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                + "  public static void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a", 82,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a", 84,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a", 82);
    }

    @Test
    public void testPureMethod() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "public class TestJava { \n"
                        + "  //@ requires i < 1000; ensures \\result == i+1;\n" 
                        + "  //@ pure \n"
                        + "  public int m(int i) { return i+1; }\n"
                        + "  public void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }\n"
                        + "  public void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }\n"
                        + "  public void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                        + "  public void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                        + "  public void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                        + "  public void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1a", 75,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2a", 77,
                "/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method m3a", 75);
    }

    @Test
    public void testPureNonFunction() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "/*@ code_bigint_math*/ public class TestJava { \n"
                        + "  public int z;\n" + "  //@ ensures \\result == z+1;\n" + "  //@ pure \n"
                        + "  public int m() { return z+1; }\n"
                        + "  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                        + "  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                        + "  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                        + "  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                        + "  public void m3(int a, int b) { z = 7; int k = z+1; /*@ assert k == m(); */ }\n"
                        + "  public void m3a(int a, int b) { z = 7; int k = z+2; /*@ assert k == m(); */ }\n" + "}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a", 52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a", 54,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m3a", 59);
    }

    @Test
    public void testPureNoArguments() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "/*@ code_bigint_math*/ public class TestJava { \n" 
                + "  public static int z;\n"
                + "  //@ ensures \\result == z+1;\n" 
                + "  //@ pure \n" 
                + "  public static int m() { return z+1; }\n"
                + "  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                + "  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                + "  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                + "  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n" + "}",
                "/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1a", 52,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2a", 54);
    }

    @Test
    public void testInheritedPost() {
        main.addOptions("-code-math=bigint");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" 
                + "abstract class TestJavaA { \n"
                + "  \n" 
                + "  //@ ensures \\result > 0;\n" 
                + "  abstract public int m(int iii);\n" 
                + "}\n"
                + "abstract class TestJavaB extends TestJavaA { \n" 
                + "  //@ also\n" 
                + "  //@ ensures \\result > ii;\n"
                + "  abstract public int m(int ii);\n" 
                + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" 
                + "  //@ also public normal_behavior\n"
                + "  //@ ensures \\result == i+1;\n" 
                + "  //@ pure\n" 
                + "  public int m(int i) { return i+1; }\n"
                + "  //@ requires a >= 0;\n" 
                + "  //@ ensures \\result == a+1;\n" 
                + "  public int n1(int a) { return m(a); }\n"
                + "  public int n1a(int a) { return m(-1); }\n" 
                + "}"
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m",25
                ,"/tt/TestJava.java:4: warning: Associated declaration", 7
                ,"/tt/TestJava.java:20: warning: There is no feasible path to program point at program exit in method tt.TestJava.n1a(int)",14
                );
    }

    @Test
    public void testInheritedPostA() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "abstract class TestJavaA { \n"
                + "  //@ requires iii > 0;\n" + "  //@ ensures \\result > 0;\n" + "  abstract public int m(int iii);\n"
                + "}\n" + "abstract class TestJavaB extends TestJavaA { \n" + "  //@ also\n"
                + "  //@ ensures \\result > ii;\n" + "  abstract public int m(int ii);\n" + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" + "  //@ also\n"
                + "  //@ ensures \\result == i+1;\n" + "  //@ pure\n" + "  public int m(int i) { return i+1; }\n"
                + "  //@ ensures \\result == a+1;\n" + "  public int n1(int a) { return m(a); }\n"
                + "  public int n1a(int a) { return m(-1); }\n" + "}");
    }

    @Test
    public void testInheritedPostB() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "abstract class TestJavaA { \n"
                + "  //@ requires iii > 0;\n" + "  //@ ensures \\result > 0;\n" + "  abstract public int m(int iii);\n"
                + "}\n" + "abstract class TestJavaB extends TestJavaA { \n" + "  //@ also\n"
                + "  //@ requires ii > 0;\n" + "  //@ ensures \\result > ii;\n" + "  abstract public int m(int ii);\n"
                + "}\n" + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" + "  //@ also\n"
                + "  //@ requires i > 0;\n" + "  //@ ensures \\result == i+1;\n" + "  //@ pure\n"
                + "  public int m(int i) { return i+1; }\n" + "}");
    }

    @Test
    public void testInheritedPre() {
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" 
                + "abstract class TestJavaA { \n"
                + "  //@ requires iii == 1;\n" 
                + "  //@ ensures \\result == iii;\n"
                + "  abstract public int m(int iii);\n" 
                + "}\n" 
                + "abstract class TestJavaB extends TestJavaA { \n"
                + "  //@ also\n" 
                + "  //@ requires ii == 2;\n" 
                + "  //@ ensures \\result == ii;\n"
                + "  abstract public int m(int ii);\n" 
                + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" 
                + "  //@ also\n"
                + "  //@ requires i == 3;\n" 
                + "  //@ ensures \\result == i;\n" 
                + "  //@ pure\n"
                + "  public int m(int i) { return i; }\n" // OK
                + "  //@ requires a >= 1 && a <= 3;\n" 
                + "  //@ ensures \\result == a;\n"
                + "  public int m1(int a) { return m(a); }\n" // OK
                + "  //@ ensures \\result == a;\n" 
                + "  public int m1a(int a) { return m(-1); }\n" // Precondition
                                                                                                    // ERROR
                + "}"
                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Precondition) in method m1a",35
                ,"/tt/TestJava.java:18: warning: Associated declaration",14
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: iii == 1",20
                ,"/tt/TestJava.java:9: warning: Precondition conjunct is false: ii == 2",19
                ,"/tt/TestJava.java:15: warning: Precondition conjunct is false: i == 3",18
                );
    }

    @Test
    public void testTrace() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  //@ requires 0<=ii && ii <=3;\n"
                + "  //@ ensures \\result < 0;\n" + "  public static int m(int ii) { \n"
                + "    if (ii==1) return -1; \n" + "    if (ii==2) return -2; \n" + "    if (ii==3) return -3; \n"
                + "    ii = 7;\n" + "    return 0; }\n" + "  //@ requires ii == 2;\n" + "  //@ ensures \\result == 0;\n"
                + "  public static int mm(int ii) { \n" + "    if (ii==1) return -1; \n"
                + "    if (ii==2) return -2; \n" + "    if (ii==3) return -3; \n" + "    ii = 7;\n"
                + "    return 0; }\n" + "  public static int is;\n" + "  //@ ensures is == 6;\n"
                + "  public static int m3(int ii) { \n" + "    try { ii = 0; \n" + "      if (ii == 0) return -2; \n"
                + "    } finally { \n" + "      is = 7;\n" + "    }" + "    return 0; }\n"
                + "  //@ ensures \\result == 1;\n" + "  public static int m4(int ii) { \n" + "    try { ii = 0; \n"
                + "      if (ii == 0) return -2; \n" + "    } finally { \n" + "      is = 7;\n" + "    }"
                + "    return 0; }\n" + "}",
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m",
                5, "/tt/TestJava.java:4: warning: Associated declaration", 7,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Postcondition) in method mm",
                16, "/tt/TestJava.java:12: warning: Associated declaration", 7,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m3",
                20, "/tt/TestJava.java:20: warning: Associated declaration", 7,
                "/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Postcondition) in method m4",
                20, "/tt/TestJava.java:27: warning: Associated declaration", 7);
    }

    @Test
    public void testForwardInit() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public static int m() { \n" + "    int c = c+1; \n"
                        + "    //@ assert c == 1; \n" + "    return c; \n" + "  }\n" + "}",
                "/tt/TestJava.java:4: variable c might not have been initialized", 13);
    }

    @Test
    public void testGhostVars() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public static int m() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ assert d + c == 9; \n" + "    return c; \n"
                        + "  }\n" + "  public static int mm() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ assert d + c == 10; \n" + "    return c; \n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method mm", 9);
    }

    @Test
    public void testSetDebug() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public static int m() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ set d = 10;\n" + "    //@ assert d + c == 14; \n"
                        + "    return c; \n" + "  }\n" + "  public static int mm() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ set d = 10;\n" + "    //@ assert d + c == 15; \n"
                        + "    return c; \n" + "  }\n" + "  public static int q() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ debug d = 10;\n" + "    //@ assert d + c == 14; \n"
                        + "    return c; \n" + "  }\n" + "  public static int qq() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ debug d = 10;\n" + "    //@ assert d + c == 15; \n"
                        + "    return c; \n" + "  }\n" + "}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method mm", 9,
                "/tt/TestJava.java:28: warning: The prover cannot establish an assertion (Assert) in method qq", 9);
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInJava() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "/*@ nullable_by_default */ public class TestJava { \n" 
                + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" 
                + "    int i = o.j; \n" 
                + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" 
                + "    int i = o.j; \n" 
                + "  }\n"
                + "  //@ requires o != null;\n" 
                + "  public static void m2(TestJava o) { \n" 
                + "    int i = o.j; \n"
                + "  }\n" 
                + "  public static void m3(TestJava o) { \n" 
                + "    boolean i = o != null && o.j == 1; \n"
                + "  }\n" 
                + "  public static void m4(TestJava o) { \n" 
                + "    boolean i = o == null || o.j == 1; \n"
                + "  }\n" 
                + "  public static void m5(TestJava o) { \n" 
                + "    int i = ( o != null ? o.j : 6); \n"
                + "  }\n" 
                + "  public static void m6(TestJava o) { \n" 
                + "    int i = ( o == null ? 7 : o.j); \n"
                + "  }\n" 
                + "  public static void m6a(TestJava o) { \n" 
                + "    int i = ( o != null ? 7 : o.j); \n"
                + "  }\n" 
                + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" 
                + "    boolean i = p(o) && o.j == 0; \n" 
                + "  }\n"
                + "  public static void m7a(TestJava o) { \n" 
                + "    boolean i = p(o) || o.j == 0; \n" 
                + "  }\n" 
                + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0",
                14,
                "/tt/TestJava.java:27: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a",
                32,
                "/tt/TestJava.java:37: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a",
                26);
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedMInJava() {
        helpTCX("tt.TestJava", "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n" + "    int i = o.z(); \n"
                + "  }\n" + "  public static void m3(TestJava o) { \n" + "    boolean i = o != null && o.z() == 1; \n"
                + "  }\n" + "  public static void m4(TestJava o) { \n" + "    boolean i = o == null || o.z() == 1; \n"
                + "  }\n" + "  public static void m5(TestJava o) { \n" + "    int i = ( o != null ? o.z() : 6); \n"
                + "  }\n" + "  public static void m6(TestJava o) { \n" + "    int i = ( o == null ? 7 : o.z()); \n"
                + "  }\n" + "  public static void m6a(TestJava o) { \n" + "    int i = ( o != null ? 7 : o.z()); \n"
                + "  }\n" + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" + "    boolean i = p(o) && o.z() == 0; \n" + "  }\n"
                + "  public static void m7a(TestJava o) { \n" + "    boolean i = p(o) || o.z() == 0; \n" + "  }\n"
                + "  //@ signals_only \\nothing; \n public int z() { return 0; }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0",
                14,
                "/tt/TestJava.java:27: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a",
                32,
                "/tt/TestJava.java:37: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a",
                26);
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedSMInJava() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n" + "    int i = o.z(); \n"
                + "  }\n" + "  public static void m3(TestJava o) { \n" + "    boolean i = o != null && o.z() == 1; \n"
                + "  }\n" + "  public static void m4(TestJava o) { \n" + "    boolean i = o == null || o.z() == 1; \n"
                + "  }\n" + "  public static void m5(TestJava o) { \n" + "    int i = ( o != null ? o.z() : 6); \n"
                + "  }\n" + "  public static void m6(TestJava o) { \n" + "    int i = ( o == null ? 7 : o.z()); \n"
                + "  }\n" + "  public static void m6a(TestJava o) { \n" + "    int i = ( o != null ? 7 : o.z()); \n"
                + "  }\n" + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" + "    boolean i = p(o) && o.z() == 0; \n" + "  }\n"
                + "  public static void m7a(TestJava o) { \n" + "    boolean i = p(o) || o.z() == 0; \n" + "  }\n"
                + "  //@ signals_only \\nothing; \n public static int z() { return 0; }\n" + "}");
    }

    /**
     * Tests whether the various kinds of undefined constructs are actually
     * detected.
     */
    @Test
    public void testUndefinedInJava2() {
        //main.addOptions("-logic=AUFNIA");
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ /*@ code_java_math spec_java_math*/ public class TestJava { \n"
                        + "  int j;\n" 
                        + "  public static void m(TestJava o) { \n" 
                        + "    int i = o.j; \n" 
                        + "  }\n  "
                        + "  public static void m1(int[] a) { \n" 
                        + "    int i = a[0]; \n" 
                        + "  }\n"
                        + "  //@ requires a != null;\n" 
                        + "  public static void m2(int[] a) { \n"
                        + "    int i = a[-1]; \n" 
                        + "  }\n" 
                        + "  //@ requires a != null;\n"
                        + "  public static void m3(int[] a) { \n" 
                        + "    //@ assume a.length == 1; \n"
                        + "    int i = a[1]; \n" 
                        + "  }\n" 
                        + "  public static void m4(int i, int j) { \n"
                        + "    int k = i/j; \n" 
                        + "  }\n" 
                        + "  public static void m5(int i, int j) { \n"
                        + "    int k = i%j; \n" 
                        + "  }\n" 
                        + "  public static void m6( RuntimeException r) { \n"
                        + "    Throwable t = r;\n" 
                        + "    Exception rr = ((Exception)t); \n" 
                        + "  }\n"
                        + "  public static void m6a(Exception r) { \n" 
                        + "    Throwable t = r;\n"
                        + "    RuntimeException rr = ((RuntimeException)t) ; \n" 
                        + "  }\n"
                        + "  public static void m7(/*@ non_null*/ RuntimeException r) { \n" 
                        + "    Throwable t = r;\n"
                        + "    Exception rr = ((Exception)t); \n" + "  }\n"
                        + "  public static void m7a(/*@ non_null*/Exception r) { \n" + "    Throwable t = r;\n"
                        + "    RuntimeException rr = ((RuntimeException)t) ; \n" + "  }\n" + "}",
                seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",
                        14,
                        anyorder(
                                seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",
                                        14),
                                seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",
                                        14)),
                        "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2",
                        14,
                        "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3",
                        14,
                        "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4",
                        14,
                        "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m5",
                        14,
                        "/tt/TestJava.java:31: warning: The prover cannot establish an assertion (PossiblyBadCast) in method m6a:  a (@org.jmlspecs.annotation.Nullable :: java.lang.Throwable) cannot be proved to be a java.lang.RuntimeException",
                        28,
                        "/tt/TestJava.java:39: warning: The prover cannot establish an assertion (PossiblyBadCast) in method m7a:  a (@org.jmlspecs.annotation.Nullable :: java.lang.Throwable) cannot be proved to be a java.lang.RuntimeException",
                        28));
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInSpec() {
        helpTCX("tt.TestJava", "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j;\n"
                + "  public static void m(TestJava o) { \n" + "    //@ assume o.j == 1; \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    //@ assume o.j == 1; \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n"
                + "    //@ assume o.j == 1; \n" + "  }\n" + "  public static void m3(TestJava o) { \n"
                + "    //@ assume o != null && o.j == 1; \n" + "  }\n" + "  public static void m4(TestJava o) { \n"
                + "    //@ assume o == null || o.j == 1; \n" + "  }\n" + "  public static void m5(TestJava o) { \n"
                + "    //@ assume o != null ==> o.j == 1; \n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17);
    }

    // FIXME - problem with types
    /**
     * Tests whether the various kinds of undefined constructs are actually
     * detected.
     */ // TODO - need pure method violating preconditions, bad array element
        // assignment
    @Test
    public void testUndefinedInSpec2() {
        //main.addOptions("-logic=AUFNIA");
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j;\n"
                        + "  public static void m(TestJava o) { \n" + "    //@ assume o.j == 1; \n" + "  }\n  "
                        + "  public static void m1(int[] a) { \n" + "    //@ assume a[0] == 1; \n" + "  }\n"
                        + "  //@ requires a != null;\n" + "  public static void m2(int[] a) { \n"
                        + "    //@ assume a[-1] == 1; \n" + "  }\n" + "  //@ requires a != null;\n"
                        + "  public static void m3(int[] a) { \n" + "    //@ assume a.length == 1; \n"
                        + "    //@ assume a[1] == 1; \n" + "  }\n" + "  public static void m4(int i, int j) { \n"
                        + "    //@ assume i/j == 4; \n" + "  }\n" + "  public static void m5(int i, int j) { \n"
                        + "    //@ assume i%j == 4; \n" + "  }\n" + "  public static void m6(RuntimeException r) { \n"
                        + "    Throwable t = r;\n" + "    //@ assume ((Exception)t) != null ? true : true; \n" // OK
                        + "  }\n" + "  public static void m6a(Exception r) { \n" + "    Throwable t = r;\n"
                        + "    //@ assume ((RuntimeException)t) != null ? true : true ; \n" + "  }\n"
                        + "  public static void m7(/*@ non_null*/RuntimeException r) { \n" + "    Throwable t = r;\n"
                        + "    //@ assume ((Exception)t) != null ? true : true; \n" + "  }\n"
                        + "  public static void m7a(/*@ non_null*/Exception r) { \n" + "    Throwable t = r;\n"
                        + "    //@ assume ((RuntimeException)t) != null ? true : true ; \n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17,
                anyorder(
                        seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1",
                                17),
                        seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",
                                17)),
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2",
                17,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3",
                17,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4",
                17,
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5",
                17,
                "/tt/TestJava.java:31: warning: The prover cannot establish an assertion (UndefinedBadCast) in method m6a:  a (@org.jmlspecs.annotation.Nullable :: java.lang.Throwable) cannot be proved to be a java.lang.RuntimeException",
                17,
                "/tt/TestJava.java:39: warning: The prover cannot establish an assertion (UndefinedBadCast) in method m7a:  a (@org.jmlspecs.annotation.Nullable :: java.lang.Throwable) cannot be proved to be a java.lang.RuntimeException",
                17);
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - loop invariants, variants, represents, signals, modifies
    // TODO - old constructs, quantifications, set comprehension, pure methods -
    // check other JMl expressions
    @Test
    public void testUndefinedInSpec3() {
        main.addOptions("-keys=DEBUG");
        helpTCX("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "/*@ nullable_by_default */ public class TestJava { \n" 
                + "  public int j = 1;\n"
                + "  public static @Nullable TestJava t;\n" 
                + "  public static void m(TestJava o) { \n"
                + "    //@ assume o.j == 1; \n" 
                + "  }\n  " 
                + "  public static void m1(TestJava o) { \n"
                + "    //@ assert o.j == 1 ? true : true; \n" 
                + "  }\n  " 
                + "  public static void m2(TestJava o) { \n"
                + "    //@ ghost int i = o.j; \n" 
                + "  }\n  " 
                + "  public static void m3(TestJava o) { \n"
                + "    //@ ghost int i; debug i = o.j; \n" 
                + "  }\n  " 
                + "  //@ requires o.j == 1;\n"
                + "  public static void m4(@Nullable TestJava o) { \n" 
                + "  }\n  "
                + "  //@ ensures t.j == 1 ? true : true;\n" 
                + "  public static void m5(TestJava o) { \n" 
                + "  }\n  "
                + "  public static void m6(TestJava o) { \n" 
                + "    //@ ghost int i; set i = o.j; \n" 
                + "  }\n  " 
                + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1",
                17,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2",
                24,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m3",
                33,
                "/tt/TestJava.java:17: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m4",
                19,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m5",
                18,
                "/tt/TestJava.java:22: warning: Associated method exit",
                4,
                "/tt/TestJava.java:24: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m6",
                31);
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - readable writable, represents, assert, other clauses
    @Test
    public void testUndefinedInSpec4() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j = 1;\n"
                        + "  static TestJava t;\n" + "  public void m(TestJava o) { \n" + "    //@ assume o.j == 1; \n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17);
    }

    @Test
    public void testUndefinedInSpec4d() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n"
                        + "  //@ public invariant t.j ==1 ? true: true;\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava",
                25,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                25);
    }

    /** Check to catch undefinedness in an initially clause */
    @Test
    public void testUndefinedInSpec4a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n"
                        + "  public boolean j = true;\n" + "  static TestJava t;\n" + "  public TestJava() { \n"
                        + "  }\n" + "  //@ public initially t.j ? true : true;\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava",
                25);
    }

    /** Check to catch undefinedness in a constraint clause */
    @Test
    public void testUndefinedInSpec4b() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n  "
                        + "  //@ public constraint t.j ==1 ? true: true;\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                28);
    }

    /** Check to catch undefinedness in a axiom clause */
    @Test
    public void testUndefinedInSpec4c() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n  "
                        + "  // @ axiom (\\forall TestJava q;; q.j ==1);\n" // FIXME
                        + "}");
    }

    @Test
    public void testUndefinedInSpec5() {
        main.addOptions("-nullableByDefault", "-no-checkAccessible");
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static TestJava t;\n" + "  int j = t.j;\n" + "}",
                "/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",
                12);
    }

    @Test
    public void testUndefinedInJava6() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  static TestJava t;\n"
                        + "  int j = 1;\n" + "  public void m1(TestJava o) { \n" + "    int i = t.j; \n" + "  }\n  "
                        + "  public void m2(TestJava o) { \n" + "    t.j = 1; \n" + "  }\n  "
                        + "  public void m3(TestJava o) { \n" + "    t.j += 1; \n" + "  }\n  "
                        + "  public void m4(TestJava o) { \n" + "    int i = 0; i += t.j; \n" + "  }\n  "
                        + "  public void m5(TestJava o) { \n" + "    assert t.j == 1 ? true : true; \n" + "  }\n  "
                        // TODO for, while, foreach, do, switch, case, if,
                        // throw, method call, index, conditional,
                        // annotation, binary, unary, conditional, new array,
                        // new class, return, synchronized
                        + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",
                14,
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2",
                6,
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3",
                6,
                "/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4",
                22,
                "/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m5",
                13);
    }

    // TODO - need tests within various Java constructs, including with
    // short-circuits

    /** This test tests catch blocks */
    @Test
    public void testCatch() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava { \n" 
                        + "  public void m() {\n" 
                        + "    int i = 0;\n"
                        + "    try {\n" 
                        + "      throw new RuntimeException();\n"
                        + "    } catch (RuntimeException e) {\n" 
                        + "      i=1;\n" 
                        + "    } catch (Exception e) {\n"
                        + "      i=2;\n" 
                        + "    }\n" 
                        + "    //@ assert i == 1;\n" 
                        + "  }\n" 
                        + "  public void ma() {\n"
                        + "    int i = 0;\n" 
                        + "    try {\n" 
                        + "      throw new RuntimeException();\n"
                        + "    } catch (RuntimeException e) {\n" 
                        + "      i=1;\n" 
                        + "    } catch (Exception e) {\n"
                        + "      i=2;\n" 
                        + "    }\n" 
                        + "    //@ assert i == 2;\n" 
                        + "  }\n" 
                        + "}",
                "/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method ma", 9);
    }

    @Test
    public void testCatch2() {
        main.addOptions("-method=ma");
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  public void mx() {\n"
                + "    int i = 0;\n" + "    try {\n" + "      throw new Exception();\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    }\n" + "    //@ assert i == 2;\n" + "  }\n" + "  public void mp() {\n"
                + "    int i = 0; int j = 0;\n" + "    try {\n" + "      throw new Exception();\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    } finally {\n" + "      j=3;\n" + "    }\n"
                + "    //@ assert i == 2 && j == 3;\n" + "  }\n" + "  public void ma() {\n" + "    int i = 0;\n"
                + "    try {\n" + "      throw new Exception();\n" + "    } catch (RuntimeException e) {\n"
                + "      i=1;\n" + "    } catch (Exception e) {\n" + "      i=2;\n" + "    }\n"
                + "    //@ assert i == 1;\n" + "  }\n" + "  public void m1(int k) {\n"
                + "    int i = 0; int j = 0; //@ assume k == 0; \n" + "    try {\n" + "      try {\n"
                + "         if (k == 0) throw new Exception();\n" + "      } finally {\n" + "         j = 50;\n"
                + "      }\n" + "      j = 60;\n" + "    } catch (RuntimeException e) {\n" + "      i=1;\n"
                + "    } catch (Exception e) {\n" + "      i=2;\n" + "    }\n" + "    //@ assert i == 2 && j == 50;\n"
                + "  }\n" + "  public void m11(int k) throws Exception {\n"
                + "    int i = 0; int j = 0; //@ assume k == 0; \n" + "    try {\n" + "    try {\n" + "      try {\n"
                + "         if (k == 0) throw new Exception();\n" + "      } finally {\n" + "         j = 50;\n"
                + "      }\n" + "      j = 60;\n" + "    } catch (RuntimeException e) {\n" + "      i=1;\n"
                + "    } finally {\n" + "      i=2;\n" + "    }\n" + "    } finally {\n"
                + "    //@ assert i == 2 && j == 50;\n" + "    }\n"

                + "  }\n" + "  public void m2() {\n" + "    int i = 20;\n" + "    try {\n" + "      i=10;\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    }\n" + "    i = 0;\n" + "    //@ assert i == 0;\n" + "  }\n"
                + "  public void m3() {\n" + "    int i = 20;\n" + "    try {\n" + "      i=10;\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    } finally {\n" + "      i = 0;\n" + "    }\n" + "    //@ assert i == 0;\n"
                + "  }\n" + "}",
                "/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Assert) in method ma", 9
        // FIXME - enventually rejuvenate dead branch detection
        // ,"/tt/TestJava.java:42: warning: else branch apparently never taken
        // in method tt.TestJava.m1(int)",14
        // ,"/tt/TestJava.java:59: warning: else branch apparently never taken
        // in method tt.TestJava.m11(int)",14
        );
    }

    @Test
    public void testCatch3() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires i == 2 && ee != null; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }


    @Test
    public void testCatch3a() {
        helpTCX("tt.TestJava",
                "package tt; //@ non_null_by_default \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires i == 2; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testCatch4() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires e != null & ee != null & ae != null;\n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires e != null & ee != null & ae != null;\n"
                        + "  //@   requires i == 2; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testTypes() {
        helpTCX("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"
                + "  public void m1(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\typeof(o) == \\typeof(o);\n" 
                + "    //@ assert \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\typeof(o) <: \\type(Object);\n" 
                + "    //@ assert \\typeof(o) <:= \\type(Object);\n" 
                + "  }\n"
                + "  public void m1a(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\typeof(o) != \\type(Object);\n" 
                + "  }\n"
                + "  public void m2(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\typeof(o) == \\type(Object);\n" 
                + "  }\n"
                + "  public void m2a(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\typeof(o) == \\type(TestJava);\n" 
                + "  }\n"
                + "  public void m3(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ assert \\type(TestJava) <: \\typeof(o);\n" 
                + "    //@ assert \\type(TestJava) <:= \\typeof(o);\n" 
                + "  }\n" 
                + "}",
                "/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m1a", 9,
                "/tt/TestJava.java:20: warning: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testTypes2() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public void m1(/*@non_null*/TestJava o) {\n"
                        + "    //@ assume \\typeof(o) == \\type(TestJava);\n"
                        + "    //@ assert \\typeof(o) <: \\type(Object);\n" + "  }\n"
                        + "  public void m2(/*@non_null*/TestJava o) {\n"
                        + "    //@ assert \\typeof(o) <: \\type(Object);\n" + "  }\n" + "}");
    }

    @Test
    public void testTypes3() {
        helpTCX("tt.TestJava",
                "package tt; import org.jmlspecs.lang.JML; \n" 
                        + "public class TestJava { \n"
                        + "  public void m1(/*@non_null*/Object o) {\n"
                        + "    //@ assert JML.erasure(\\typeof(o)) == o.getClass();\n" 
                        + "  }\n" 
                        + "}");
    }

    @Test
    public void testSignals1() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 0;\n"
                + "  public void m1() throws Exception {\n" + "    if (i==0) throw new Exception();\n" + "  }\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 1;\n" // FAILS
                + "  public void m1a() throws Exception {\n" + "    if (i==0) throw new Exception();\n" + "  }\n" + "}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a",
                15, "/tt/TestJava.java:12: warning: Associated declaration", 7);
    }

    @Test
    public void testSignals2() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 0;\n" // OK
                + "  public void m2() throws Exception {\n" + "    if (i==0) throw new Exception();\n" + "  }\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (RuntimeException e) i == 1;\n" // FAILS
                + "  public void m2a() throws Exception {\n" + "    if (i==0) throw new RuntimeException();\n" + "  }\n"
                + "}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2a",
                15, "/tt/TestJava.java:12: warning: Associated declaration", 7);
    }

    @Test
    public void testSignals3() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 0;\n"
                        + "  public void m3() throws RuntimeException {\n"
                        + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "  //@ requires i >= 0;\n"
                        + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 1;\n" // FAILS
                        + "  public void m3a() throws RuntimeException {\n"
                        + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "}",
                "/tt/TestJava.java:14: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",
                15, "/tt/TestJava.java:12: warning: Associated declaration", 7);
    }

    @Test
    public void testSignals4() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (RuntimeException e) i == 1;\n" // OK
                                                                                                                        // because
                                                                                                                        // a
                                                                                                                        // RuntimeException
                                                                                                                        // is
                                                                                                                        // never
                                                                                                                        // thrown
                + "  public void m4() throws Exception {\n" + "    if (i==0) throw new Exception();\n" + "  }\n" + "}");
    }

    @Test
    public void testSignalsOnly() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static int i;\n"
                        + "  //@ signals_only java.io.IOException;\n" // FAILS
                        + "  public void m1a() throws Exception {\n" + "    if (i==0) throw new Exception();\n"
                        + "  }\n" + "  //@ signals_only \\nothing;\n" // FAILS
                        + "  public void m2a() {\n" + "    if (i==0) throw new RuntimeException();\n" + "  }\n"
                        + "  //@ signals_only Exception;\n" // OK
                        + "  public void m3() {\n" + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "}",
                "/tt/TestJava.java:6: warning: The prover cannot establish an assertion (ExceptionList) in method m1a",
                15, "/tt/TestJava.java:4: warning: Associated declaration", 7,
                "/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ExceptionList) in method m2a",
                15, "/tt/TestJava.java:8: warning: Associated declaration", 7);
    }

    @Test
    public void testConstraint() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1();\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint2() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for ! m1();\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint3() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for \\everything;\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint3a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for !\\nothing;\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint4() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for \\nothing;\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint4a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for !\\everything;\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m2() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint6() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i);\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint7() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1(), m1(int);\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m1(int j) {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14,
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: warning: Associated declaration", 14);
    }

    @Test
    public void testConstraint7a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1(), m1(int);\n" + "  public static void m1() {\n"
                        + "  }\n" + "  public static void m1(int j) {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint8() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for ! m1(), m1(int);\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m1(int j) {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint9() {
        expectedExit = 1;
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ public constraint i > \\old(i) for TestJava();\n" + "  public TestJava() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:4: Constructors are not allowed as methods in non-static constraint clauses", 41);
    }

    @Test
    public void testConstraint9a() {
        helpTCX("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ public constraint i > \\old(i);\n" + "  public TestJava() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint10() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public static constraint i > \\old(i) for TestJava();\n" + "  public TestJava() {\n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: warning: Associated declaration", 21);
    }

    @Test
    public void testConstraint10a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public static constraint i > \\old(i);\n" + "  public TestJava() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: warning: Associated declaration", 21);
    }

    @Test
    public void testConstraint11() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "interface A { \n" + "  //@ ghost static public int i = 0;\n"
                        + "  //@ public static constraint i > \\old(i);\n" + "}\n"
                        + "public class TestJava implements A { \n" + "  public TestJava() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: warning: Associated declaration", 21);
    }

    @Test
    public void testConstraint11a() {
        helpTCX("tt.TestJava",
                "package tt; \n" + "interface A { \n" + "  //@ ghost static public int i = 0;\n"
                        + "  //@ public constraint i > \\old(i);\n" + "}\n" + "public class TestJava implements A { \n"
                        + "  public TestJava() {\n" + "  }\n" + "}");
    }

    @Test // FIXME - for reasons unknown, this test appears to be
            // non-deterministic - sometimes succeeding sometimes failing
    public void testMethodAxioms() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (i > 0 && i < 10);\n" 
                        + "  //@ pure\n"
                        + "  //@ model public boolean m(int i);\n"

                        + "  public void mm() {\n" 
                        + "  //@ assert (\\forall int k; 3<k && k <7; m(k));\n"
                        + "  //@ assert (\\forall int k; 3<k && k <7; m(k-1));\n"
                        + "  //@ assert !(\\forall int k; -3<k && k <7; m(k));\n" 
                        + "  }\n" 
                        + "}");
    }

    @Test
    public void testMethodAxioms2() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (i > 0 && i < 10);\n" 
                        + "  //@ pure function\n"
                        + "  //@ model public static boolean m(int i);\n"

                        + "  //@ pure\n" 
                        + "  public void mm() {\n"
                        + "  //@ assert !(\\forall int k; 3<k && k <11; m(k));\n" 
                        + "  }\n" + "}"
            //    ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method mm", 7
                        );
    }

    @Test
    public void testMethodAxioms2a() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (i > 0 && i < 10);\n" 
                        + "  //@ pure\n"
                        + "  //@ model public boolean m(int i);\n"

                        + "  //@ pure\n" 
                        + "  public void mm() {\n"
                        + "  //@ assert !(\\forall int k; 3<k && k <11; m(k));\n" 
                        + "  }\n" + "}"
            //    ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method mm", 7
                        );
    }

    @Test 
    public void testNullityAndConstructors() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  private /*@ spec_public */ char[] o; \n"
                        + "  \n" 
                        + "  //@ assignable \\everything;\n "
                        + "  public TestJava(final /*@ non_null */ char[] the_array) {\n"
                        + "      o = new char[the_array.length]; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testNullityAndConstructors2() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  private /*@ spec_public */ char[] o; \n"
                        + "  \n" 
                        + "  //@ assignable \\everything;\n "
                        + "  public TestJava(final /*@ non_null */ char[] the_array) {\n"
                        + "      o = new char[the_array.length]; \n"
                        + "      System.arraycopy(the_array, 0, o, 0, the_array.length); \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test 
    public void testNullityAndConstructors3() {
            main.addOptions("-nonnullByDefault");
            helpTCX("tt.TestJava",
                    "package tt; \n" 
                            + "public class TestJava  { \n" 
                            + "  private /*@ spec_public */ char[] o; \n"
                            + "  private /*@ spec_public */ int[] oo; \n" 
                            + "  \n" 
                            + "  //@ assignable \\everything;\n "
                            + "  public TestJava(final /*@ non_null */ char[] the_array) {\n"
                            + "      o = the_array; \n" 
                            + "  }\n" 
                            + "}"
                    ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (NullField) in method TestJava", 36
                    );
    }

    @Test
    public void testArrayLength() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m(final byte[] array) {\n"
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength2() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ requires k >= 0;\n"
                        + "  public void m(int k) {\n"
                        + "      short[] array = new short[k]; \n" 
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "      //@ assert array.length == k; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength3() {
        main.addOptions("-nonnullByDefault","-method=m");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  long[] array;\n"
                        + "  public void m() {\n"
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength4() {
        main.addOptions("-nonnullByDefault","-method=m");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "      char[] array = mm(); \n" 
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "  public abstract char[] mm();\n" 
                        + "}"
                );
    }

    @Test
    public void testVarargs() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);\n"
                        + "  public void mm(int... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(new int[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(new int[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargsX() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0); requires n == -2;\n"
                        + "  public void mm(int n, int... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(-2); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(-2,1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-2,-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(-2,1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-2,-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(-2,new int[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(-2,new int[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargs2() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);\n"
                        + "  public void mm(Integer... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(new Integer[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(new Integer[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargs2X() {
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);"
                        + "      requires n == -2;\n"
                        + "  public void mm(int n, Integer... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(-2); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(-2,1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-2,-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(-2,1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-2,-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(-2,new Integer[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(-2,new Integer[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: warning: Associated declaration",15
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test // Incorrect syntax for \lbl produced an exception, but I could not reproduce that behavior here
    public void testLblError() {
        expectedExit = 1;
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  public void m0(int i, int j) {\n"
                        + "      //@ assert (\\lbl I i) + \\lbl(J j) == 0; \n" 
                        + "  }\n" 
                        + "}"
                        ,"/tt/TestJava.java:4: Expected a comma or right parenthesis here",38
                        ,"/tt/TestJava.java:4: Incorrectly formed or terminated assert statement near here",38
                );
    }

    @Test
    public void testNewLblSytax() {
        expectedExit = 0;
        main.addOptions("-nonnullByDefault");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  public void m0(int i, int j) {\n"
                        + "      //@ assert (\\lbl I i) + \\lbl(J,j) == 0; \n" 
                        + "  }\n" 
                        + "}"
                        ,"/tt/TestJava.java:4: warning: Label I has value 0",24
                        ,"/tt/TestJava.java:4: warning: Label J has value ( - 1 )",36
                        ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m0",11
                );
    }

    @Test
    public void testExitInfo2() {
        expectedExit = 0;
        main.addOptions("-escExitInfo","-escMaxWarnings=10");
        helpTCX("tt.TestJava",
                "package tt; //@ nullable_by_default \n" 
                        + "public class TestJava  { \n" 
                        + "  /*@ requires o != null; \n"
                        + "      ensures \\result == (j>=0); \n"
                        + "     pure function */ public static boolean positive(Object o, int j) { \n"
                        + "         return j >= 0; }\n"
                        + "  public int j; \n"
                        + "  //@ signals (NullPointerException e) positive(null,j); \n"
                        + "  //@ signals (NegativeArraySizeException e) positive(null,j); \n"
                        + "  public void m0(int i, Object o) {\n"
                        + "      if (i == 1) { j = -2; throw new NullPointerException(); }\n" 
                        + "           if (i == 2) { j = -1; throw new NegativeArraySizeException(); }\n" 
                        + "  }\n" 
                        + "}"
                        ,anyorder(seq(
                 "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m0",54
                ,"/tt/TestJava.java:5: warning: Associated declaration",45
                ,"/tt/TestJava.java:12: warning: Associated method exit",34
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: o != null",18
                ),seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m0",48
                ,"/tt/TestJava.java:5: warning: Associated declaration",45
                ,"/tt/TestJava.java:11: warning: Associated method exit",29
                ,"/tt/TestJava.java:3: warning: Precondition conjunct is false: o != null",18
                ))
                );
    }

    @Test
    public void testExitInfo() {
        expectedExit = 0;
        main.addOptions("-escExitInfo","-escMaxWarnings=3");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int j; \n"
                        + "  //@ ensures j >= 0; \n"
                        + "  public void m0(int i, Object o) {\n"
                        + "      j = -1; \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m0",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testFinalInvariant2() {
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == 19; static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 19; pure\n"
                        + "  public int mmm() { return ii; }"
                        + "}"
                );
    }

    @Test
    public void testFinalInvariant1() {
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int jj = 21; \n"
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == 19 && jj == 21; static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 21; pure\n"
                        + "  public int mmm() { return jj; }"
                        + "}"
                );
    }


    @Test
    public void testFinalInvariant3() {
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == mm(); static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 19; pure\n"
                        + "  public int mmm() { return ii; }"
                        + "}"
                );
    }

    @Test
    public void testFinalInvariant() {
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        + "  //@ public final invariant ii == 19; \n"
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        + "}"
                        ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii",27
                        ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii",27
//                        ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",8
//                        ,"/tt/TestJava.java:4: warning: Associated declaration",20
                                );
    }

    @Test
    public void testEnumStaticInitializer() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public enum TestJava  { \n" 
                        + "    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }\n"
                        + "    private int bit;\n"
                        + "    static /*@ spec_public */ private int num = 10;\n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   ensures num == 10; \n"
                        + "  //@   ensures A.bit == 1; \n"
                        + "  //@   ensures B.bit == 2; \n"
                        + "  //@ static_initializer \n"
                        + "  public void m() {}"
                        + "}\n"
                        ,"/tt/TestJava.java:8: An identifier with private visibility may not be used in a ensures clause with public visibility",18
                        ,"/tt/TestJava.java:9: An identifier with private visibility may not be used in a ensures clause with public visibility",18
                        );
    }

    @Test
    public void testEnumStaticInitializer2() {
        expectedExit = 0;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public enum TestJava  { \n" 
                        + "    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }\n"
                        + "    /*@ spec_public */ private int bit;\n"
                        + "    static /*@ spec_public */ private int num = 10;\n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   ensures num == 10; \n"
                        + "  //@   ensures A.bit == 1; \n"
                        + "  //@   ensures B.bit == 2; \n"
                        + "  //@ static_initializer \n"
                        + "  public void m() {}"
                        + "}\n"
                        );
    }
    
    @Test
    public void testNonNullElements() {
        expectedExit = 0;
        main.addOptions("-code-math=bigint");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires \\nonnullelements(arr); \n"
                        + "  public static void m( Key... arr) {\n"
                        + "     int s = 0;\n"
                        + "     for (Key i: arr) {\n"
                        + "        s = s + i.k;\n"
                        + "     }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testShowStatementESC() {
        expectedExit = 0;
        main.addOptions("-code-math=bigint","-method=m","-escMaxWarnings=1");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i, j+1;\n"
                        + "     int k = i+j;\n"
                        + "     //@ show k;\n"
                        + "     //@ assert k > 0;\n"
                        + "     int m = i-j;\n"
                        + "     //@ show m,k;\n"
                        + "     //@ assert m > 0;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:7: warning: Show statement expression i has value 0",15
                        ,"/tt/TestJava.java:7: warning: Show statement expression j + 1 has value 2",18
                        ,"/tt/TestJava.java:9: warning: Show statement expression k has value 1",15
                        ,"/tt/TestJava.java:12: warning: Show statement expression m has value ( - 1 )",15
                        ,"/tt/TestJava.java:12: warning: Show statement expression k has value 1",17
                        ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m",10
                        );
    }

    @Test
    public void testShowStatement() {
        expectedExit = 0;
        main.addOptions("-lang=jml");
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:7: warning: The show statement construct is an OpenJML extension to JML and not allowed under -lang=jml",10
                        ,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The \\count construct is an OpenJML extension to JML and not allowed under -lang=jml",37
                  ); 
    }

    @Test
    public void testShowStatementErrors() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i;\n"
                        + "     //@ show \n"
                        + "     //@ show i i;\n"
                        + "     //@ show;\n"
                        + "     //@ show i\n"
                        + "     //@ show %;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:8: warning: Inserting missing semicolon at the end of a show statement",14
                        ,"/tt/TestJava.java:9: Bad syntax in the expression list in show statement",17
                        ,"/tt/TestJava.java:11: warning: Inserting missing semicolon at the end of a show statement",15
                        ,"/tt/TestJava.java:12: illegal start of expression",15
                        ,"/tt/TestJava.java:12: illegal start of expression",16
                        );
    }

    @Test
    public void testArrayCopy() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <: \\type(Key); \n"
                        + "  public static void m(Key[] k) {\n"
                        + "     Key[] kk = java.util.Arrays.copyOfRange(k,0,k.length);\n"
                        + "     //@ assert kk != null;\n"
                        + "     //@ assert \\nonnullelements(kk);\n"
                        + "     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testArrayCopy2() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <: \\type(Key); \n"
                        + "  public static void m(Key[] k) {\n"
                        + "     Key[] kk = java.util.Arrays.<Key>copyOfRange(k,0,k.length);\n"
                        + "     //@ assert kk != null;\n"
                        + "     //@ assert \\nonnullelements(kk);\n"
                        + "     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);\n"
                        + "  }\n"
                        + "}\n"
                        );
    }


    @Test  // FIXME - crashes
    public void testDuplicateGhost() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "  //@ ghost int k = 1;\n"
                        + "  //@ ghost int k = 2;\n"
                        + "  }\n"
                        + "}\n"
                 ,"/tt/TestJava.java:5: variable k is already defined in method m()",17
                        );
    }

    @Test
    public void testChainedCompare() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "  //@ ghost int i = 2;\n"
                        + "  //@ assert 0 <= i < 10 < 12;\n"
                        + "  //@ set i = 10;\n"
                        + "  //@ assert !(0 <= i < 10);\n"
                        + "  //@ assert 0 <= i < 11 == 2 <= i <= 12;\n"
                        + "  //@ assert 11 >= i+1 > 1 == 12 >= i > 2;\n"
                        + "  //@ assert 11 >= i+1 < 12;\n"
                        + "  //@ assert 11 >= i+1 < 12 == true;\n"
                        + "  //@ assert 11 >= i+1 > 1 != 12 <= i <= 22;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:10: warning: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:11: warning: Cannot chain comparisons that are in different directions",17
                        );
    }

    @Test
    public void testAllowForbid2() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  //@ signals_only \\nothing;\n"
                        + "  public void m(/*@ nullable */ TestJava t) {\n"
                        + "    int i = t.iii //@ allow NullPointerException; \n"
                        + "    ;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (ExceptionList) in method m",14
                        ,"/tt/TestJava.java:4: warning: Associated declaration",7
                        );
    }

    @Test
    public void testAllowForbid3() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t) {\n"
                        + "    int i = t.iii //@ forbid NullPointerException; \n"
                        + "    ;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",14
                        );
    }

    @Test
    public void testAllowForbid5() {
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii; //@ ignore NullPointerException; \n"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testAllowForbid4() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii; //@ ignore java.lang.XX; \n"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:5: cannot find symbol\n" + 
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang",41
                        ,"/tt/TestJava.java:5: cannot find symbol\n" +  // TODO: It is a OpenJDK problem that this error message is repeated
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang",41
                        );
    }

    @Test
    public void testAllowForbid() {
        expectedExit = 1;
        helpTCX("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t) {\n"
                        + "  int i = t.iii //@ allow NullPointerException; \n"
                        + "  ;\n"
                        + "  int j = t.iii; //@ forbid NullPointerException; \n"
                        + "  int k = t.iii; //@ forbid X; \n"
                        + "  k = t.iii; //@ forbid ; \n"
                        + "  k = t.iii; //@ forbid NullPointerException \n"
                        + "  k = t.iii; //@ forbid NullPointerException, ArrayIndexOutOfBoundsException; \n"
                        + "  k = t.iii; //@ forbid NullPointerException ArrayIndexOutOfBoundsException; \n"
                        + "  k = t.iii; //@ forbid NullPointerException; allow NullPointerException \n"
                        + "  k = t.iii; //@ ignore NullPointerException; allow NullPointerException \n"
                        + "  k = t.iii; //@ ignore NullPointerException; forbid NullPointerException \n"
                        + "  k = t.iii; //@ forbid java.lang.NullPointerException \n"
                        + "  k = t.iii //@ forbid java.lang. \n"
                        + "  ;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:9: warning: Ignoring annotation with no exceptions listed",25
                        ,"/tt/TestJava.java:10: warning: A line annotation should end with a semicolon",46
                        ,"/tt/TestJava.java:13: warning: A line annotation should end with a semicolon",74
                        ,"/tt/TestJava.java:14: warning: A line annotation should end with a semicolon",74
                        ,"/tt/TestJava.java:15: warning: A line annotation should end with a semicolon",75
                        ,"/tt/TestJava.java:16: warning: A line annotation should end with a semicolon",56
                        ,"/tt/TestJava.java:17: Expected an identifier here in the line annotation",35
                        ,"/tt/TestJava.java:8: cannot find symbol\n" + 
                                 "  symbol:   class X\n" + 
                                 "  location: class tt.TestJava",29
                        );
    }
    
    @Test
    public void testJMLDataGroup() {
    	helpTCX("tt.C",
    			"package tt; /*@ non_null_by_default */ public class C {\n"
    			+ "    //@ public model JMLDataGroup g;\n"
    			+ "}\n"
    			);
    }

}
