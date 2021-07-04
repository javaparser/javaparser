package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esccode extends EscBase {

    public esccode(String options, String solver) {
        super(options,solver);
    }
    

    @Test
    public void testCode1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ also public normal_behavior\n"
                +"  //@    ensures \\result > 0;\n"
                +"  public int m() {\n"
                +"    return 5;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:11: warning: Associated declaration",10
                );
    }

    @Test
    public void testCode2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ also public normal_behavior\n"
                +"  //@    ensures \\result > 0;\n"
                +"  public int m() {\n"
                +"    return 5;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testCode3() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ also public normal_behavior\n"
                +"  //@    ensures \\result > 0;\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",10
                );
    }

    @Test
    public void testCode4() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ also public code normal_behavior\n"
                +"  //@    ensures \\result > 0;\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",10
                );
    }

    @Test
    public void testCode5() {
        main.addOptions("-method=n"); // This is part of the test, not debugging
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int n() {\n"
                +"    return m();\n"
                +"  }\n"
                +"  //@ also public code normal_behavior\n"
                +"  //@    ensures true;\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method n",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",10
                );
    }

    @Test
    public void testCode6() {
        main.addOptions("-method=n"); // This is part of the test, not debugging
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int n() {\n"
                +"    return m();\n"
                +"  }\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                );
    }


    @Test
    public void testCode7() {
        main.addOptions("-method=n"); // This is part of the test, not debugging
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result >= 10;\n"
                +"  public int n() {\n"
                +"    return m();\n"
                +"  }\n"
                +"  //@ also public code normal_behavior\n"
                +"  //@    ensures \\result >= 10;\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures true;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testCode8() {
        main.addOptions("-method=n"); // This is part of the test, not debugging
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result >= 10;\n"
                +"  public int n() {\n"
                +"    return m();\n"
                +"  }\n"
                +"  //@ also public normal_behavior\n"
                +"  //@    ensures \\result >= 10;\n"
                +"  public int m() {\n"
                +"    return 0;\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures true;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                );
    }
    

    @Test
    public void testCode9() {
        main.addOptions("-method=n"); // This is part of the test, not debugging
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava extends A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int n() {\n"
                +"    return m();\n"
                +"  }\n"
                +"}\n"
                +" class A { \n"
                +"  //@ public code normal_behavior\n"
                +"  //@    ensures \\result > 10;\n"
                +"  public int m() {\n"
                +"    return 20;\n"
                +"  }\n"
                +"}"
                );
    }

}
