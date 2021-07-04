package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** This class of JUnit tests checks various uses of generic types.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escgeneric extends EscBase {


    public escgeneric(String options, String solver) {
        super(options,solver);
    }

    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }
    

    @Override
    public void setUp() throws Exception {
        //print = true;
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //JmlEsc.escdebug = false;
        main.addOptions("-timeout=30");
        main.addOptions("-jmltesting");
    }
    
    @Test
    public void testConstructor() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void mx(Integer i) {\n"
                +"    Object oo = new TestG<Integer>(i);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    Object oo = new TestG<Object>(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ;\n"
                +"  public TestG(E i) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method mx",17
                ,"/tt/TestJava.java:12: warning: Associated declaration",10
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
                );
    }
    
    /** Tests that we can reason about the result of \\typeof */
    @Test
    public void testTypeOf() {
    	main.addOptions("-checkFeasibility=all");  // Part of test
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert \\typeof(this) <: \\type(TestJava);\n"
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    //@ assume \\typeof(this) == \\type(Object);\n"
                +"    //@ assert false;\n" // should not trigger
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    //@ assert \\typeof(this) == \\type(Object);\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: There is no feasible path to program point after explicit assume statement in method tt.TestJava.ma(java.lang.Object)",9
                ,"/tt/TestJava.java:8: warning: There is no feasible path to program point before explicit assert statement in method tt.TestJava.ma(java.lang.Object)",9
                ,"/tt/TestJava.java:6: warning: There is no feasible path to program point at program exit in method tt.TestJava.ma(java.lang.Object)",15
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (Assert) in method mb",9
                );
    }

    @Test
    public void testGenericType() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T> extends B<T> { \n"
                +"  public void ma(T i) {\n"
                +"  }\n"
                +"}\n"
                +"class A<T> extends TestJava<B<T>> { \n"
                +"  public void mb(T i) {\n"
                +"  }\n"
                +"}\n"
                +"class B<E> {}\n"
                +"class C<F> extends java.util.LinkedList<B<F>> {}\n"
        );
    }
    
    @Test
    public void testGenericType2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ assert i instanceof Object;\n"
                +"    //@ assert \\typeof(i) <: \\type(Object);\n" // Line 6
                +"    //@ assert \\erasure(\\typeof(i)) <: \\erasure(\\type(Object));\n"
                +"    //@ assert \\typeof(i) <: \\type(T);\n"
                +"    //@ assert i instanceof B;\n"
                +"    //@ assert \\erasure(\\typeof(i)) <: \\erasure(\\type(B));\n"
                +"    //@ assert \\typeof(i) <: \\type(B);\n" // Line 11
                +"    //@ assert \\erasure(\\typeof(i)) <: \\erasure(\\type(C));\n" // false
               +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ assert i instanceof Object;\n"
                +"    //@ assert \\typeof(i) <: \\type(C);\n" // false
                +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType2b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(T i) {\n"
                +"    //@ assume i != null;\n"
                +"    //@ assert i instanceof Object;\n"
                +"    //@ assert \\type(T) <: \\type(B);\n" // true
                +"    //@ assert \\type(T) <: \\type(C);\n" // false
                +"  }\n"
                +"  /*@ public normal_behavior ensures true; pure */ public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C extends TestJava<B> {}\n"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m",9
        );
    }
    
    @Test
    public void testGenericType1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava<T extends B> { \n"
                
                +"  public void m(Integer i) {\n"
                +"    //@ assert Object.class == java.lang.Object.class;\n"
                +"    //@ assert \\type(TestJava<Integer>) != \\type(Object);\n"
                +"    //@ assert \\type(TestJava<Integer>) != \\type(TestJava<Object>);\n"
                +"  }\n"
                +"  public void mz(Object o) {\n"
                +"    //@ assert Object.class == \\erasure(\\type(T));\n" // NO
                +"  }\n"
                +"  public void ma(Object o) {\n"
                +"    //@ assert \\type(TestJava<Integer>) == \\type(TestJava<T>);\n"  // NO
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    //@ assert \\typeof(this) == \\type(Object);\n"  // NO
                +"  }\n"
                +"  public void mc(Object o) {\n"
                +"    //@ assert \\type(TestJava<Integer>) == \\type(TestJava<Object>);\n"  // NO
                +"  }\n"
                +"  public void mz1(Object o) {\n"
                +"    //@ assert Object.class != \\erasure(\\type(T));\n"  // OK because T extends B so can't be Object
                +"  }\n"
                +"  public TestJava() {}\n"
                +"}\n"
                +"class B {}\n"
                +"class C {}\n"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method mz",9
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assert) in method ma",9
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (Assert) in method mb",9
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (Assert) in method mc",9
        );
    }

    @Test
    public void testStatic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.<Integer>mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.<Object>mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ;\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",22
                ,"/tt/TestJava.java:12: warning: Associated declaration",26
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
        );
    }

    @Test
    public void testStaticB() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) != \\type(Integer) ;\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",13
                ,"/tt/TestJava.java:12: warning: Associated declaration",26
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) != \\type(Integer)",25
        );
    }

    @Test
    public void testStatic2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.<Integer>mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.<Object>mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) == \\type(Integer) ;\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Precondition) in method mb",21
                ,"/tt/TestJava.java:12: warning: Associated declaration",26
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) == \\type(Integer)",25
        );
    }

    @Test
    public void testStatic2B() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  public void ma(Integer i) {\n"
                +"    TestG.mm(i);\n"
                +"  }\n"
                +"  public void mb(Object o) {\n"
                +"    TestG.mm(o);\n"
                +"  }\n"
                +"}\n"
                +"class TestG {\n"
                +"  //@ requires \\type(E) == \\type(Integer) ;\n"
                +"  public static <E> void mm(E t) {}\n"
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Precondition) in method mb",13
                ,"/tt/TestJava.java:12: warning: Associated declaration",26
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) == \\type(Integer)",25
        );
    }

    @Test
    public void testTypeParameter() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/ TestG<Integer> i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/ TestG<Object> i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"    //@ requires \\type(E) != \\type(Integer);\n"
                +"    public void mm(E t) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:12: warning: Associated declaration",17
                ,"/tt/TestJava.java:11: warning: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
    
    @Test
    public void testTypeParameter2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void ma(/*@ non_null*/TestG<Integer>.TestH i, Integer j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mb(/*@ non_null*/TestG<Object>.TestH i, Object j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"  public void mc(/*@ non_null*/TestG<String>.TestH i, String j) {\n"
                +"    i.mm(j);\n"
                +"  }\n"
                +"}\n"
                +"class TestG<E> {\n"
                +"  class TestH  {\n"
                +"    //@ requires \\type(E) != \\type(Integer);\n"
                +"    public void mm(E t) {}\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Precondition) in method ma",9
                ,"/tt/TestJava.java:16: warning: Associated declaration",17
                ,"/tt/TestJava.java:15: warning: Precondition conjunct is false: \\type(E) != \\type(Integer)",27
                );
    }
 
    @Test
    public void testUnboxing() {
        main.addOptions("-method=m");  // Just test method m
        helpTCX("tt.TestJava"," class A { void m(/*@non_null*/ Integer ooo) { \n "
                +"int sum = 0; \n"
                +"{ /*@ assume ooo >= 0; */ sum += ooo; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test
    public void testForEach3() {
        helpTCX("tt.TestJava"," class A {  /*@ code_bigint_math spec_bigint_math */ void m(/*@non_null*/ java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (Integer o: list) { /*@ assume o != null && o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                );
    }

    @Test
    public void testForEach3a() {
        helpTCX("tt.TestJava"," class A { /*@ code_bigint_math spec_bigint_math */ void m(/*@non_null*/ java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m",13
                );
    }

    @Test
    public void testForEach3bad() {
        helpTCX("tt.TestJava"," class A { /*@ code_bigint_math spec_bigint_math */ void m(/*@non_null*/ java.util.List<Integer> list) { \n "
                +"int sum = 0; \n"
                +"//@ loop_invariant sum >= 0; \n"
                +"for (int o: list) { /*@ assume o >= 0; */ sum += o; }  \n"
                +"//@ assert sum >= 0; \n"
                +"}}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m",13
                );
    }

    @Test
    public void testElemType() {
        helpTCX("tt.TestJava"," class A { void m(/*@ non_null */ char[] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(char); \n"
                +"}}"
                );
    }

    @Test
    public void testElemType2() {
        helpTCX("tt.TestJava"," class A { void m(/*@ non_null */ char[] a) { \n"
                +"//@ assert \\elemtype(\\typeof(a)) == \\type(int); \n"
                +"}}"
                ,"/tt/TestJava.java:2: warning: The prover cannot establish an assertion (Assert) in method m",5
                );
    }

    @Test
    public void testGenericThrow() {
        main.addOptions("-method=rt"); // Just test method rt
        helpTCX("tt.TestJava",
        		 "public class TestJava { \n"
        	    +" //@ public exceptional_behavior \n"
        	    +" //@   requires true; \n"  // FIXME - should be t instanceof T
        	    // Can't say signals_only T; because JML only deals with Exception, not Throwable
        	    +" public static <T extends Throwable> RuntimeException rt(/*@ non_null*/ Throwable t) throws T { throw (T)t; } \n"
                +"}"
                );
    }

    
}
    
