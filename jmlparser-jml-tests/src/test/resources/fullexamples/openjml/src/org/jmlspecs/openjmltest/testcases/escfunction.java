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

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfunction extends EscBase {

    public escfunction(String options, String solver) {
        super(options,solver);
    }
    
    @Parameters
    static public Collection<String[]> parameters() {
        return EscBase.parameters();
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-nullableByDefault"); // Because the tests were written this way
        //main.addOptions("-trace");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
 
    
    
    @Test // FIXME - for reasons unknown, this test appears to be non-deterministic - sometimes succeeding sometimes failing
    public void testMethodAxioms() {
        helpTCX("tt.TestJava","package tt; \n"
                +" //@ code_java_math spec_java_math \n"
                +"public class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"  //@ pure\n"
                +"  //@ model public boolean m(int i);\n"
                
                +"  public void mm() {\n"
                +"  //@ assert (\\forall int k; 3<k && k <7; m(k));\n"
                +"  //@ assert (\\forall int k; 3<k && k <7; m(k-1));\n"
                +"  //@ assert !(\\forall int k; -3<k && k <7; m(k));\n"
                +"  }\n"
                +"}"
                );
    }

    
    @Test
    public void testMethodAxioms2() { 
        helpTCX("tt.TestJava","package tt; \n"
                +" //@ code_java_math spec_java_math \n"
                +"public class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"  //@ pure\n"
                +"  //@ model public boolean m(int i);\n"
                
                +"  //@ pure\n"
                +"  public void mm() {\n"
                +"  //@ assert !(\\forall int k; 3<k && k <11; m(k));\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testFunction() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.* ; \n"
                +"public @Immutable class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"   @Function  \n"
                +"  //@ model public boolean mfunc(int i);\n"
                
                +"  int n; \n"
                +"  public void mm() {\n"
                +"  //@ assert mfunc(5);\n"
                +"  //@ assert !mfunc(0);\n"
                +"  }\n"
                +"}"
                );
    }

    @Test
    public void testFunctionError3() { 
    	expectedExit = 1;
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.* ; \n"
                +"public class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ assignable n; \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"  @Function  \n"
                +"  //@ model public boolean mfunc(int i);\n"
                
                +"  int n; \n"
                +"  public void mm() {\n"
                +"  //@ assert mfunc(5);\n"
                +"  //@ assert !mfunc(0);\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: Function methods are implicitly pure and may not assign to any fields: n",18
                ,"/tt/TestJava.java:6: A non-static function method must be a member of a Immutable class", 3
        		);
    }

    @Test
    public void testFunctionError2() { 
    	expectedExit = 1;
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.* ; \n"
                +"public @Immutable class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ assignable n; \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"  @Function  \n"
                +"  //@ model public boolean mfunc(int i);\n"
                
                +"  int n; \n"
                +"  public void mm() {\n"
                +"  //@ assert mfunc(5);\n"
                +"  //@ assert !mfunc(0);\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: Function methods are implicitly pure and may not assign to any fields: n",18
                );
    }

    @Test
    public void testFunctionError() { 
    	expectedExit = 1;
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.* ; \n"
                +"public @Immutable class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ assignable n; \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"   \n"
                +"  //@ model function public boolean mfunc(int i);\n"
                
                +"  int n; \n"
                +"  public void mm() {\n"
                +"  //@ assert mfunc(5);\n"
                +"  n = 0;\n"
                +"  //@ assert !mfunc(n);\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:4: Function methods are implicitly pure and may not assign to any fields: n",18
                );
    }

    
    @Test
    public void testStaticFunction() { 
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.* ; \n"
                +"public class TestJava  { \n"
                +"  //@ normal_behavior \n"
                +"  //@ ensures \\result == (i > 0 && i < 10);\n"
                +"  @Pure @Function  \n"
                +"  //@ static model public boolean mfunc(int i);\n"
                
                +"  int n; \n"
                +"  public void mm() {\n"
                +"  //@ assert mfunc(5);\n"
                +"  n = 0;\n"
                +"  //@ assert !mfunc(n);\n"
                +"  }\n"
                +"}"
                );
    }

    
}

