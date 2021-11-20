package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

import java.util.function.Function;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esclambdas extends EscBase {

    public esclambdas(String options, String solver) {
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
    
    @Test
    public void testIterable1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { if (i>0) i--; i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                // FIXME - the column location is wrong - it is not clear that the possible null value is an element of the iterable, with the element being the receiver of the bump call in the foreach loop
                ,"$SPECS/specs/java/lang/Iterable.jml:41: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",40
                );
    }
    
    @Test @Ignore // not working yet
    public void testIterable1b() {
    	main.addOptions("-code-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test @Ignore // not working yet
    public void testIterable2() {
    	main.addOptions("-code-math=java"); // Just to avoid ovcerflow errors
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.Nullable MMM> a) {\n"  // We do not know that each element returned by the iterable is non-null
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",19
                );
    }
    
    @Test @Ignore // not working yet
    public void testIterable2b() {
    	main.addOptions("-code-math=java"); // Just to avoid ovcerflow errors
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"    public void bump() { i++; }\n"
                +"  }\n"
                
                +"  public void m1(/*@ non_null*/ Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"
                +"    a.forEach(m->m.bump());\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testIterable3() {
        main.addOptions("-code-math=java","-spec-math=java");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int j;\n"
                +"  public int k() { return 7; };\n"
                +"  public static class MMM {\n"
                +"    public int i ;\n"
                +"  }\n"
                
                +"  public void bump(MMM m1, MMM m2) {"
                +"     m1.i += (j + m2.i + k());\n"
                +"  }\n"
                
                +"  //@ requires a.containsNull == false;\n"
                +"  public void m1(/*@ non_null*/ Iterable<MMM> a) {\n"
                +"    a.forEach(m->bump(m,m));\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    
    @Test  @Ignore // FIXME - not working yet
    public void testIdentity() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  //@ public normal_behavior\n"
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Function<Integer,Integer> f = Function.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test @Ignore // FIXME - not working yet
    public void testIdentity2() {
        helpTCX("tt.TestJava","package tt; import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  //@ public normal_behavior\n"
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static <T> T m1(T i) {\n"
                                +"    Function<T,T> f = Function.<T>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test
    public void testIdentity3() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {\n"
                                +"  //@   public model_program {\n"
                                +"  //@      return t;\n"
                                +"  //@    }\n"
                                +"  //@ pure function\n"
                                +"  public T apply(T t);\n"
                                +"  }\n"

                                +"  static /*@ immutable */ public interface Fun<T,R> {\n"
                                +"     //@ public normal_behavior ensures true; pure function \n"
                                +"     static <T> Identity<T> identity() { return (x -> x); }\n"
                                +"  }\n"
                                
                                +"  //@ public normal_behavior\n"  // Line 14
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Identity<Integer> f = Fun.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test
    public void testIdentity4() {
        helpTCX("tt.TestJava","package tt;  import java.util.function.Function;\n"
                                +"public class TestJava { \n"
                                
                                +"  public /*@ immutable */ static interface Identity<T> extends Fun<T,T> {\n"
                                +"  //@   public normal_behavior \n"
                                +"  //@      ensures \\result == t;\n"
                                +"  //@ pure function\n"
                                +"  public T apply(T t);\n"
                                +"  }\n"

                                +"  static /*@ immutable */ public interface Fun<T,R> {\n"
                                +"     //@ public normal_behavior ensures true; pure function\n"
                                +"     static <T> Identity<T> identity() { return (x->x); }\n"
                                +"  }\n"
                                
                                +"  //@ public normal_behavior\n"  // Line 13
                                +"  //@   ensures \\result == i;\n"
                                +"  //@ pure\n"
                                +"  public static Integer m1(Integer i) {\n"
                                +"    Identity<Integer> f = Fun.<Integer>identity();\n"
                                +"    return f.apply(i);\n"
                                +"  }\n"
                                                
                                +"}"
                                );
                    }

    @Test @Ignore // not working yet
    public void testIterable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public static class MMM {\n"
                +"    public boolean i = false;\n"
                +"    //@ public normal_behavior assignable i; ensures i == !\\old(i) ;\n"
                +"    public void bump() { i = !i; }\n"
                +"  }\n"
                
                +"  //@ requires a != null;\n"
                +"  public void m1(Iterable<@org.jmlspecs.annotation.NonNull MMM> a) {\n"  // NonNull should shut off the error message
                +"    a.forEach(MMM::bump);\n"
                +"  }\n"
                                
                +"}"
                );
    }
    
    @Test
    public void testMethodReference() {
        helpTCX("tt.TestJava","package tt; import java.util.function.*; \n"
                +"@org.jmlspecs.annotation.CodeBigintMath public class TestJava { \n"
                
                +"  public int field;\n"

                +"  //@ requires j < 1000 && j > -1000;\n"
                +"  //@ assignable field;\n"
                +"  //@ ensures \\result == j+101;\n"
                +"  //@ ensures field == j+100;\n"
                +"  public int m1(/*@{FF}*/ BiFunction<TestJava,Integer,Integer> a, int j) {\n"
                +"   final /*@{FF}*/ BiFunction<TestJava,Integer,Integer>  b = a;\n"
                +"    return (int)b.apply(this,(Integer)(j+100));\n"
                +"  }\n"

                +"  /*@ @FunctionalInterface model public static interface FF extends BiFunction<TestJava,Integer,Integer> {  \n"
                +"        also assignable t.field; ensures t.field == n; ensures \\result == n+1;  \n"
                +"        non_null  \n"
                +"       Integer apply(TestJava t, Integer n);} */\n"
                
                +"    //@ public normal_behavior assignable field; ensures \\result == i + 1 && field == i ;\n"
                +"    public Integer bump(Integer i) { field = i; return i+1; }\n"
                +"    //@ public normal_behavior assignable field; ensures \\result == i + 1 ;\n"
                +"    public Integer bump2(Integer i) {  return i+1; }\n"
                
                // A different implementation in JmlParser is needed when the cast is at the very beginning of
                // the declaration (not signaled by modifiers). If we use a { then it looks like the start of a block.
                +"  //@ requires j < 1000 && j > -1000;\n"
                +"  //@ assignable field;\n"
                +"  public int m3(/*@{FF}*/ BiFunction<TestJava,Integer,Integer> a, int j) {\n"
                +"    /*@!FF*/ BiFunction<TestJava,Integer,Integer>  b = a;\n"
                +"    return (int)b.apply(this,(Integer)(j+100));\n"
                +"  }\n"
                                
                +"  //@ assignable field;\n"
                +"  public void m2() {\n"
                +"    m1(TestJava::bump, 200);\n"
                +"    //@ assert field == 300;\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test  // FIXME - using references or lambdas in these contexts is not Java
    public void testEquality() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                                
                +"  //@ public normal_behavior requires true;\n"
                +"  public static void m() {\n"
                +"    //@ ghost boolean b;"
                +"    //@ set b = RuntimeException::new == RuntimeException::new;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = RuntimeException::new != null;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = null != RuntimeException::new;\n"
                +"    //@ assert b;\n"
                +"    //@ set b = null != (java.util.function.Function)(x -> x);\n"
                +"    //@ assert b;\n"
                +"    //@ set b = java.util.function.Function::identity != (java.util.function.Function)(x -> x);\n"
                +"    //@ assert b;\n"
                +"  }\n"
                +"}"
                );
    	
    }
    
    @Test 
    public void testReplacementType() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static class C {};\n"
                +"  //@ public model static class R extends C {};\n"
                
                +"  public /*@ nullable {R}*/C field;\n"

                +"  public void set( /*@{R}*/C f) { field = f; }\n"
                                
                +"  //@ public normal_behavior requires true;\n"
                +"  public void m() {\n"
                +"    //@ assert field == null || field instanceof R;"
                +"  }\n"
                +"}"
                );
    	
    }
    
    @Test 
    public void testReplacementType2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public static class C {};\n"
                +"  public static class R extends C {};\n"
                
                +"  public /*@ nullable {R}*/C field;\n"

                +"  public void set( /*@{R}*/C f) { field = f; }\n"
                                
                +"  //@ public normal_behavior requires true;\n"
                +"  public void m() {\n"
                +"    //@ assert field == null || field instanceof R;"
                +"  }\n"
                +"}"
                );
    	
    }
    
    @Test
    public void testConstructor() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface ExFactory {\n"
                +"    //@ public normal_behavior\n"
                +"    //@   ensures \\result instanceof NullPointerException;\n"
                +"    public RuntimeException create();\n"
                +"  }\n"

                +"  public ExFactory exx;\n"
                +"  \n"
                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == ex;\n"
                +"  public TestJava(ExFactory ex) {\n"
                +"     exx = ex;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == RuntimeException::new;\n"
                +"  public TestJava() {\n"
                +"     exx = RuntimeException::new ;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ assignable exx;\n"
                +"  //@ ensures exx == ex;\n"
                +"  public void set(ExFactory ex) {\n"
                +"     exx = ex;\n"
                +"  }\n"
                                
                +"  //@ public normal_behavior\n"
                +"  //@ assignable exx;\n"
                +"  //@ ensures exx == NullPointerException::new;\n"
                +"  public void set() {\n"
                +"     exx = NullPointerException::new ;\n"
                +"  }\n"
                
				+"  //@ public exceptional_behavior requires true; signals_only NullPointerException;\n"
				+"  public static void m() {\n"
				+"    TestJava t = new TestJava(NullPointerException::new);\n"
				+"    t.set(NullPointerException::new);\n"
				+"    throw t.exx.create();\n"
				+"  }\n"

				+"  //@ public exceptional_behavior requires true; signals_only NullPointerException;\n"
				+"  public static void mm() {\n"
				+"    TestJava t = new TestJava(NullPointerException::new);\n"
				+"    t.set();\n"
				+"    throw t.exx.create();\n"
				+"  }\n"
                
                +"}"
                );
    }
    
    
    @Test
    public void testConstructor2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface ExFactory {\n"
                +"    //@ public normal_behavior\n"
                +"    //@   ensures \\result instanceof NullPointerException;\n"
                +"    public RuntimeException create();\n"
                +"  }\n"

                +"  public ExFactory exx;\n"
                +"  \n"
                
                +"  //@ public normal_behavior\n"
                +"  //@ ensures exx == NullPointerException::new;\n"
                +"  public TestJava() {\n"
                +"     exx = NullPointerException::new ;\n"
                +"  }\n"
                                
                +"  //@ public exceptional_behavior requires true; signals_only ArithmeticException;\n"
                +"  public static void m() {\n"
                +"    TestJava t = new TestJava();\n"
                +"    throw t.exx.create();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (ExceptionList) in method m",5
                ,"/tt/TestJava.java:16: warning: Associated declaration",50
                );
    }
    
    @Test
    public void testCast() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface PureSupplier<T> extends java.util.function.Supplier<T> {\n"
                +"    //@ also public normal_behavior\n"
                +"    //@   requires true;\n"
                +"    //@ pure\n"
                +"    @Override public T get();\n"
                +"  }\n"

                +"  //@ public behavior requires true; pure\n"   // Line 10
                +"  public static /*@ nullable */ Boolean m(java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"
                
                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean mm(PureSupplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"

                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean  mmm(/*@ {java.util.function.Supplier.Pure<Boolean>}*/ java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"   // Line 20
                +"  }\n"
                
                +"  //@ public normal_behavior requires true; pure\n"
                +"  public static boolean  mmmm(/*@ {java.util.function.Supplier.PureNonNull<Boolean>}*/ java.util.function.Supplier<Boolean> s) {\n"
                +"      return s.get();\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Assignable) in method m:  \\everything",19
                ,"/tt/TestJava.java:10: warning: Associated declaration",14
                ,"/tt/TestJava.java:20: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method mmm",7
                
                );
    }
    
    @Test
    public void testCast2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  @FunctionalInterface\n"
                +"  public static interface PureSupplier extends java.util.function.Supplier<Integer> {\n"
                +"    //@ also public normal_behavior\n"
                +"    //@   requires true;\n"
                +"    //@ pure\n"
                +"    @Override public Integer get();\n"
                +"  }\n"

                +"  //@ public behavior ensures true; pure\n" 
                +"  public static /*@!PureSupplier */ java.util.function.Supplier<Integer> m() {\n"
                +"      return /*@ ( PureSupplier )@*/ ()->1;\n"
                +"  }\n"
                
                +"  //@ public behavior ensures true; pure\n" 
                +"  public static /*@!PureSupplier*/ java.util.function.Supplier<Integer> mm() {\n"
                +"      return ()->1;\n"  // Also OK because the lambda expression conforms to PureSupplier as a functional interface
                +"  }\n"
                
                +"}"
                );
    }
    
    @Test
    public void testLambda() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ public model_program { return x -> x; }\n"
                +"  public static java.util.function.Function<Integer,Integer> m() { return x -> x; }\n"
                +"  }\n"
                );
    }
    
    @Test
    public void testBindLambda() {
        main.addOptions("-method=mm"); // Part of test
//        main.addOptions("-show");
        main.addOptions("-code-math=bigint","-spec-math=bigint");  // Part of test
        // @ nullableByDefault
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"      public Object ppp; \n"

                +"  public void mm(Object ppp) {\n"
                +"      boolean b = m(ppp, x->{return this.ppp;}); \n"
                +"       //@ assert b;\n"  // Should be false
                +"  }\n"
                +"  //@ inline \n"
                +"  final public boolean m(Object aaa, /*@ non_null */ java.util.function.Function<Object,Object> f) {\n"
                +"       Object a = aaa; return a != f.apply(null);"
                +"  }\n"
                +"  }\n"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method mm",12
                );
    }
    
    @Test
    public void testBindLambdaA() {
        main.addOptions("-method=mm");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        // @ nullableByDefault
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"      public Object ppp; \n"

                +"  //@ requires ppp == this.ppp;\n"
                +"  public void mm(Object ppp) {\n"
                +"      boolean b = m(ppp, x->{return this.ppp;}); \n"
                +"       //@ assert b;\n"  // Should be true
                +"  }\n"
                +"  //@ inline \n"
                +"  final public boolean m(Object aaa, /*@ non_null */ java.util.function.Function<Object,Object> f) {\n"
                +"       Object a = aaa; return a == f.apply(null);"
                +"  }\n"
                +"  }\n"
                );
    }
    
    @Test
    public void testBindLambdaB() {
        main.addOptions("-method=mm");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        //@ nullableByDefault
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"      public Object ppp; \n"

                +"  public void mm(Object ppp) {\n"
                +"      boolean b = m(this.ppp, x->{return this.ppp;}); \n"
                +"       //@ assert b;\n"
                +"  }\n"
                +"  //@ inline \n"
                +"  final public boolean m(Object aaa, /*@ non_null */ java.util.function.Function<Object,Object> f) {\n"
                +"       Object a = aaa; return a == f.apply(null);"
                +"  }\n"
                +"  }\n"
                );  // No errors
    }
    
    @Test
    public void testBindLambdaC() {
        main.addOptions("-method=mm");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        //@ nullableByDefault
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"      public Object ppp; \n"

                +"  public void mm(Object ppp) {\n"
                +"      boolean b = m(this.ppp, x->{return x;}); \n"
                +"       //@ assert b;\n"
                +"  }\n"
                +"  //@ inline \n"
                +"  final public boolean m(Object aaa, /*@ non_null */ java.util.function.Function<Object,Object> f) {\n"
                +"       Object a = aaa; return a == f.apply(this.ppp);"
                +"  }\n"
                +"  }\n"
                );  // No errors
    }
    
    @Test
    public void testBindLambdaD() {
        main.addOptions("-method=mm");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        //@ nullableByDefault
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"      public Object ppp; \n"

                +"  public void mm(Object ppp) {\n"
                +"      boolean b = m(this.ppp, x->x); \n"
                +"       //@ assert b;\n"  // SHould be true
                +"  }\n"
                +"  //@ inline \n"
                +"  final public boolean m(Object aaa, /*@ non_null */ java.util.function.Function<Object,Object> f) {\n"
                +"       Object a = aaa; return a == f.apply(this.ppp);"
                +"  }\n"
                +"  }\n"
                );
    }
    
    @Test
    public void testBindLambda2() {
        main.addOptions("-method=mm");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ non_null_by_default*/ public class TestJava { \n"
                +"      public int a = 11; \n"

                +"  //@ requires this.a == 11;\n"
                +"  public void mm() {\n"
                +"      int a = 9; \n"
                +"      int b = a + m(a, this.a, x->{return x+a+this.a+100;}); \n"
                +"       //@ assert b == 9 + 7 + 11 + (11+9+11+100);\n"
                +"  }\n"
                +"  //@ inline \n"
                +"  final public int m(int aa, int b, /*@ non_null */ java.util.function.Function<Integer,Integer> f) {\n"
                +"       int a = 7; return a + b + f.apply(this.a);"
                +"  }\n"
                +"  }\n"
                );  // No errors
    }
    
    @Test
    public void testBindLambda21() {
        main.addOptions("-method=m");
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        helpTCX("tt.TestJava","package tt; import java.util.function.Function; \n"
                +"/*@ non_null_by_default*/ public class TestJava { \n"
                +"      //@ model public static interface NNFunction<T,R> extends Function<T,R> { non_null R apply(non_null T t); } \n"
                +"      public int a = 11; \n"

                +"  //@ requires this.a == 11;\n"
                +"  public void mm() {\n"
                +"      int a = 9; \n"
                +"      int b = a + m(a, this.a, x->{return x+a+this.a+100;}); \n"
                +"       //@ assert b == 9 + 7 + 11 + (11+9+11+100);\n"
                +"  }\n"
                +"  //@ requires f != null; inline \n"
                +"  final public int m(int aa, int b, /*@{NNFunction<Integer,Integer>}*/ Function<Integer,Integer> f) {\n"
                +"       int a = 7; return a + b + f.apply(this.a);"
                +"  }\n"
                +"  }\n"
                );  // No errors
    }
    
    @Test
    public void testBindLambdaByte() {
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  private /*@ spec_public nullable */ Byte aaaaaaaaaaa = null; \n"

                +"      //@ assignable this.aaaaaaaaaaa;\n"
                +"      //@ ensures this.aaaaaaaaaaa != null;\n"
                +"      //@ ensures this.aaaaaaaaaaa.byteValue() == aaaaaaaaaaa;\n"
                +"  public void mm(byte aaaaaaaaaaa) {\n"
                +"      //this.aaaaaaaaaaa = aaaaaaaaaaa;\n"
                +"      set(()->this.aaaaaaaaaaa = aaaaaaaaaaa);\n"
                +"  }\n"
                +"  //@ public model static interface NoException { public normal_behavior ensures true; void run(); } \n"
                +"  //@ public normal_behavior requires true; { r.run(); } ensures true; \n"
                +"  public void set(/*@{NoException}*/ Runnable r) {\n"
                +"       r.run();"
                +"  }\n"
                +"}\n"
                );  // No errors
    }
    
    @Test
    public void testBindLambdaInt() {
        main.addOptions("-code-math=bigint","-spec-math=bigint");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public /*@ nullable */ Integer aaaaaaaaaaa = null; \n"

                +"      //@ assignable this.aaaaaaaaaaa;\n"
                +"      //@ ensures this.aaaaaaaaaaa != null;\n"
                +"      //@ ensures this.aaaaaaaaaaa.intValue() == aaaaaaaaaaa;\n"
                +"  public void mm(int aaaaaaaaaaa) {\n"
                +"      set(()->this.aaaaaaaaaaa = aaaaaaaaaaa);\n"
                +"  }\n"
                +"  //@ public behavior requires true; { r.run(); } ensures true; \n"
                +"  public void set(Runnable r) {\n"
                +"       r.run();"
                +"  }\n"
                +"}\n"
                );  // No errors
    }
    

}
