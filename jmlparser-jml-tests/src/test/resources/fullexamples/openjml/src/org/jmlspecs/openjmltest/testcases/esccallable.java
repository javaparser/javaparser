package org.jmlspecs.openjmltest.testcases;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esccallable extends EscBase {

    public esccallable(String options, String solver) {
        super(options,solver);
    }
    
    @Test
    public void testBasicCallable() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testBasicCallable3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  public void m() { n(); }\n"
                +"  void n() {}\n"
                +"}"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n() is not callable",22
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                         ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                                 ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                                 )
                );
    }

    @Test
    public void testBasicCallable4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { p(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.p() is not callable",15
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                                ,seq("/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                                        ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                          )
                );
    }

    @Test
    public void testBasicCallable5() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n;\n"
                +"  void m() { B.n(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                         ,seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",30
                                 ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                         )
                );
    }

    @Test
    public void testBasicCallable6() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable TestJava.n;\n"
                +"  void m() { B.n(); }\n"
                +"  static void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                         ,seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",30
                                 ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable6a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable TestJava.n;\n"
                +"  void m() { B.n(); }  //@ nowarn Callable;\n"
                +"  static void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",30
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable6b() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable TestJava.n; //@ nowarn Callable;\n"
                +"  void m() { B.n(); } \n"
                +"  static void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} };\n"
                );
    }

    @Test
    public void testBasicCallable6c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable TestJava.n;\n"
                +"  void m() { B.n(); }  //@ nowarn Callable;\n"
                +"  static void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { public static void n() {} }; //@ nowarn Callable;\n"
                );
    }

    @Test
    public void testBasicCallable7() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable B.n;\n"
                +"  void m() { B.n(); }\n"
                +"  void n() {}\n"
                +"  void p() {}\n"
                +"}\n"
                +"class B { \n"
                +"  //@ callable \\nothing;\n"
                +"  public static void n() {} };\n"
                );
    }

    @Test
    public void testBasicCallable8() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable9() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(int i) {}\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n(int) is not callable",15
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable10() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable n(Object);\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n(java.lang.Object) is not callable",16
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int),n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable n(Object);\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable11a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int),n(Object);\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",16
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11b() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\everything;\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable11c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  void m() { n(1); }\n"
                +"  //@ callable \\everything;\n"
                +"  void n(int i) {}\n"
                +"  void n(Object o) {}\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n(int) is not callable",15
                                ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                         ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",16
                                 ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable11d() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\nothing;\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n(int) is not callable",15
                            ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                          ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                                    ,"/tt/TestJava.java:3: warning: Associated declaration",7)
                           )
                );
    }

    @Test
    public void testBasicCallable11e() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(int);\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11f() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable \\everything;\n"
                +"  void m() { n(1); }\n"
                +"  void n(int i) {}\n" // default callable everything
                +"  void n(Object o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable12() {  // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n();\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable12a() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object,Object);\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable13() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m() { n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable14() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable15() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object[] o) { n(o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable16() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ callable n(Object[]);\n"
                +"  void m(Object o) { n(o,o); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n(Object ... o) {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable20() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable21() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  //@ callable \\nothing;\n"
                +"  void n() {}\n"
                +"}\n"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n() is not callable",32
                ,"/tt/TestJava.java:6: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                ,anyorder(seq("/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Callable) in method m:  tt.TestJava.n() is not callable",32
                                ,"/tt/TestJava.java:6: warning: Associated declaration",7)
                            ,seq("/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                                    ,"/tt/TestJava.java:6: warning: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable21c() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Callable) in method m:  \\everything is not callable",8
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21b() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n();\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\everything;\n"
                +"  void m(boolean b) { if (!b) n(); }\n"
                +"  void n() {}\n" // default callable everything
                +"}\n"
                );
    }

    @Test
    public void testBasicCallable22() { // OK
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ requires b;\n"
                +"  //@ callable n(boolean);\n"
                +"  //@ also requires !b;\n"
                +"  //@ callable \\nothing;\n"
                +"  void m(boolean b) { if (b) n(!b); }\n"
                +"  //@ requires q; callable p();\n"
                +"  //@ also requires !q; callable \\nothing;\n"
                +"  void n(boolean q) {}\n"
                +"  void p() {}\n"
                +"}\n"
                );
    }

}
