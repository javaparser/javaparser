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
public class racnewLoops extends RacBase {

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
        main.addOptions("-code-math=java","-spec-math=java");  // FIXME - errors if we use bigint sermsantics
        //main.addOptions("-verboseness=4");
        expectedNotes = 0;
    }
    
    // FIXME - needs more tests with break and continue, including nested loops
    // Also tests with \count and \values

    @Test public void testForLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i <9 ; \n" +
                "    //@ decreases 10-i; \n" +
                "    for (int i=0; i<10; i++) ; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:4: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:4: JML loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:4: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:4: JML loop invariant is false at beginning of loop body"
                ,"END"
                );
    }

    @Test public void testForLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i <= 10 ; \n" +
                "    //@ decreases 7-i; \n" +
                "    for (int i=0; i<10; i++) ; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:5: JML loop variant is negative"
                ,"/tt/TestJava.java:5: JML loop variant is negative"
                ,"END"
                );
    }

    @Test public void testForLoopIndex() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i == \\count ; \n" +
                "    //@ decreases 10-\\count; \n" +
                "    for (int i=0; i<10; i++) ; \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    @Test public void testForNested() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    //@ loop_invariant i <= 10 ; \n" +
                "    for (int i=0; i<10; i++) {\n" +
                "      //@ ghost int save = \\count;\n" +
                "      //@ loop_invariant \\count <= save; \n" +
                "      for (int j=0; j<i; j++) {" +
                "          ; \n" +
                "      }\n" +
                "    }\n" +
                "  } " +
                "}"
                ,"END"
                );
    }


    @Test public void testForEachLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    int[] a = new int[10];\n" +
                "    //@ ghost int i = 0; \n" +
                "    //@ loop_invariant i <= a.length ; \n" +
                "    //@ decreases a.length-i; \n" +
                "    for (int j: a) { \n" +
                "       //@ set i = i + 1;\n" +
                "    }\n" +
                "} " +
                "}"
                ,"END"
                );
    }
    @Test public void testForEachLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                " m(); System.out.println(\"END\"); } \n" +
                " static void m() { \n" +
                "    int[] a = new int[10];\n" +
                "    //@ ghost int i = 0; \n" +
                "    //@ loop_invariant i < a.length ; \n" +
                "    //@ decreases a.length-i-2; \n" +
                "    for (int j: a) { \n" +
                "       //@ set i = i + 1;\n" +
                "    }\n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:7: JML loop variant is negative"
                ,"/tt/TestJava.java:6: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:6: JML loop invariant is false at beginning of loop body"
                ,"END"
                );
    }

    
    @Test public void testLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    while (i>0) --i; \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    @Test public void testLoopIndex() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i + \\count == \\old(i); \n" +
                "    //@ decreases i; \n" +
                "    while (i>0) --i; \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    
    @Test public void testLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); m(-1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    System.out.println(\"VALUE \" + i); \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    while (i>=0) --i; \n" +
                "} " +
                "}"
                ,"VALUE 5"
                ,"/tt/TestJava.java:5: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:5: JML loop invariant is false at beginning of loop body"
                ,"VALUE 0"
                ,"/tt/TestJava.java:5: JML loop invariant is false at end of loop body"
                ,"/tt/TestJava.java:5: JML loop invariant is false at beginning of loop body"
                ,"VALUE -1"
                ,"/tt/TestJava.java:5: JML loop invariant is false before entering loop"
                ,"/tt/TestJava.java:5: JML loop invariant is false at beginning of loop body"
                ,"END"
                );
    }

    @Test public void testLoop3() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i-2; \n" +
                "    while (i>0) --i; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:5: JML loop variant is negative"
                ,"END"
                );
    }

    @Test public void testLoop4() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases 10-i; \n" +
                "    while (i>0) --i; \n" +
                "} " +
                "}"
                ,"/tt/TestJava.java:5: JML loop variant does not decrease"
                ,"END"
                );
    }

    @Test public void testLoop5() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(7); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    while (i>0) { System.out.println(\"VALUE \" + i); \n" +
                "        --i; \n" +
                "        if (i == 4) continue;\n" +
                "        --i; }" +
                "} " +
                "}"
                ,"VALUE 7"
                ,"VALUE 5"
                ,"VALUE 4"
                ,"VALUE 2"
                ,"END"
                );
    }

    
    @Test public void testDoLoop() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    do { --i; } while (i>0); \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    @Test public void testDoLoopIndex() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    /*@ loop_invariant i + \\count == \\old(i); */" +
                "    do {  --i; } while (i>0); \n" +
                "} " +
                "}"
                ,"END"
                );
    }

    @Test public void testDoLoopIndexBad() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    //@ decreases i; \n" +
                "    /*@ loop_invariant i + \\count == \\old(i); */" +
                "    do {  --i; --i; } while (i>0); \n" +
                "    //@ assert i == -1;\n" +
                "} " +
                "}"
                ,"END"
                );
    }

    
    @Test public void testDoLoop2() {
        helpTCX("tt.TestJava","package tt; public class TestJava { public static void main(String[] args) { \n" +
                "m(5); m(0); m(-1); System.out.println(\"END\"); } \n" +
                " static void m(int i) { \n" +
                "    System.out.println(\"VALUE \" + i); \n" +
                "    //@ loop_invariant i>= 0; \n" +
                "    //@ decreases i; \n" +
                "    do { --i; } while (i>=0); \n" +
                "} " +
                "}"
                ,"VALUE 5"
                ,"VALUE 0"
                ,"VALUE -1"
                ,"/tt/TestJava.java:5: JML loop invariant is false before entering loop"
                ,"/tt/TestJava.java:5: JML loop invariant is false at beginning of loop body"
                ,"/tt/TestJava.java:6: JML loop variant is negative"
                ,"END"
                );
    }

    

    @Test public void testForIter1() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list); }"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForIter1bad() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { java.util.List<Integer> list = new java.util.LinkedList<Integer>(); list.add(0); m(list);}"
                +"static void m(java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) {  sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }

    @Test public void testForEach4() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{1,2,3}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test public void testForEach4bad() {
        helpTCX("tt.A","package tt; class A { public static void main(String[] args) { Integer[] aa = new Integer[]{0,0,0}; m(aa); }"
                +"static void m(Integer[] list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum > 0; \n"
                +"}}"
                ,"/tt/A.java:5: JML assertion is false"
                );
    }




}
