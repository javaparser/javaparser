package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

//FIXME _ need to test when inline body is in separate file
//FIXME _ need to test when inline body is in separate file that is not parsed on the command-line
// FIXME - need to test when inline is in .jml
// FIXME - need to test when inline is in .jml for a binary class

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escinline extends EscBase {

    public escinline(String options, String solver) {
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
    
    @Test // basic test of inlining, checking assignable and ensures and return value
    public void testInline1() {
        main.addOptions("-defaults=constructor:pure");
        helpTCX("tt.TestJava","package tt; //@ code_java_math spec_java_math \n"
                +"public class TestJava { \n"
                
                +"  public int j;\n"
                +"  //+OPENJML@ inline\n"
                +"  public final int minline(int i) {\n"
                +"    j = j -1;\n"
                +"    return i + 1;\n"
                +"  }\n"
                
                +"  //@ ensures j + 1 ==  \\old(j);\n"
                +"  //@ ensures  \\result == ii + 1;\n"
                +"  //@ ensures j + \\result == ii + \\old(j);\n"
                +"  //@ assignable j;\n"
                +"  public int m1(int ii) {\n"
                +"    return minline(ii);\n"
                +"  }\n"
                                
                +"  //@ assignable j;\n"
                +"  public int m2(int ii) {\n"
                +"    return minline(ii);\n"
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n" // ERROR
                +"  public int m3(int ii) {\n"
                +"    return minline(ii);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m3:  j", 7
                ,"/tt/TestJava.java:20: warning: Associated declaration", 7
                );
    }
    
    @Test // basic test of inlining, checking assignable and ensures, with no return
    public void testInline1a() {
        helpTCX("tt.TestJava","package tt; //@ code_java_math spec_java_math \n"
                +"public class TestJava { \n"
                
                +"  public int j;\n"
                +"  //+OPENJML@ inline\n"
                +"  public final void minline(int i) {\n"
                +"    j = j + i;\n"
                +"  }\n"
                
                +"  //@ ensures j ==  \\old(j) + ii;\n"
                +"  //@ assignable j;\n"
                +"  public void m1(int ii) {\n"
                +"    minline(ii);\n"
                +"  }\n"
                                
                +"  //@ assignable \\nothing;\n" // ERROR
                +"  public void m3(int ii) {\n"
                +"    minline(ii);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m3:  j", 7
                ,"/tt/TestJava.java:13: warning: Associated declaration", 7
                );
    }
    
    // This test is OK with bigint math (cf. testInline2a), but not with java math.  FIXME - problem is that m.j does not have a range restriction assumption
    @Test  // inlining from a different class (with a different 'this')
    public void testInline2() {
        main.addOptions("-defaults=constructor:pure");
        helpTCX("tt.TestJava","package tt; //@ code_java_math spec_java_math \n"
                +" class M { \n"
                +"  public int j;\n"
                +"  //+OPENJML@ inline \n"
                +"  public int minline(int i) {\n"
                +"    j = j -1;\n"
                +"    return i + 1;\n"
                +"  }\n"
                +"}\n"
                
                +"//@ code_java_math spec_java_math \n"
                +"public class TestJava { \n"
                
                +"  \n"
                
                +"  //@ ensures m.j + 1  ==  \\old(m.j) ;\n"   // Line 13
                +"  //@ ensures  \\result == ii + 1;\n"
                +"  //@ assignable m.j;\n"
                +"  public int m1(M m, int ii) {\n"
                +"    return m.minline(ii);\n"    // Line 17
                +"  }\n"
                                
                +"  //@ assignable m.j;\n"
                +"  public int m2(M m, int ii) {\n"
                +"    return m.minline(ii);\n"
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n" // ERROR
                +"  public int m3(M m, int ii) {\n"
                +"    return m.minline(ii);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:4: warning: Inlined methods should be final since overriding methods will be ignored: minline", 15
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m3:  j", 7
                ,"/tt/TestJava.java:23: warning: Associated declaration", 7
                );
    }
    
    @Test  // inlining from a different class (with a different 'this')
    public void testInline2a() {
        helpTCX("tt.TestJava","package tt; //@ code_bigint_math spec_bigint_math \n"
                +" class M { \n"
                +"  public int j;\n"
                +"  //+OPENJML@ inline\n"
                +"  public int minline(int i) {\n"
                +"    j = j -1;\n"
                +"    return i + 1;\n"
                +"  }\n"
                +"}\n"
                
                +"//@ code_bigint_math spec_bigint_math \n"
                +"public class TestJava { \n"
                
                +"  public int j;\n"
                
                +"  //@ ensures m.j + 1 ==  \\old(m.j);\n"   // Line 13
                +"  //@ ensures  \\result == ii + 1;\n"
                +"  //@ assignable m.j;\n"
                +"  public int m1(M m, int ii) {\n"
                +"    return m.minline(ii);\n"    // Line 17
                +"  }\n"
                                
                +"  //@ assignable m.j;\n"
                +"  public int m2(M m, int ii) {\n"
                +"    return m.minline(ii);\n"
                +"  }\n"
                
                +"  //@ assignable \\nothing;\n" // ERROR
                +"  public int m3(M m, int ii) {\n"
                +"    return m.minline(ii);\n"
                +"  }\n"
                                
                +"}"
                ,"/tt/TestJava.java:4: warning: Inlined methods should be final since overriding methods will be ignored: minline", 15
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assignable) in method m3:  j", 7
                ,"/tt/TestJava.java:23: warning: Associated declaration", 7
                );
    }
    
    @Test // inline is an extension and should be final
    public void testInline3() {
    	main.addOptions("-lang=jml");
        helpTCX("tt.TestJava","package tt; //@ code_java_math spec_java_math \n"
                +" class M { \n"
                +"  public int j;\n"
                +"  //+OPENJML@ inline\n"
                +"  public int minline(int i) {\n"
                +"    j = j -1;\n"
                +"    return i + 1;\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: warning: The inline construct is an OpenJML extension to JML and not allowed under -lang=jml", 15
                ,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The \\count construct is an OpenJML extension to JML and not allowed under -lang=jml",37
                ,"/tt/TestJava.java:4: warning: Inlined methods should be final since overriding methods will be ignored: minline", 15
                );
    }
                
    @Test // inline not allowed on constructor
    public void testInline4() {
    	expectedExit = 1;
        helpTCX("tt.TestJava","package tt; //@ code_java_math spec_java_math \n"
                +" class M { \n"
                +"  public int j;\n"
                +"  //+OPENJML@ inline\n"
                +"  public M(int i) {\n"
                +"    j = i + 1;\n"
                +"  }\n"
                +"}\n"
                ,"/tt/TestJava.java:4: This JML modifier is not allowed for a constructor declaration", 15
                );
    }
                

}
