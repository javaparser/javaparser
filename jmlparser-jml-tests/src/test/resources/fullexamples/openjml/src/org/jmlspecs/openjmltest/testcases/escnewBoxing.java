package org.jmlspecs.openjmltest.testcases;

import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnewBoxing extends EscBase {

    public escnewBoxing(String options, String solver) {
        super(options,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //print = true;
    }
    
    @Test
    public void testSimple() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  \n"
                +"  public void m1good() {\n"
                +"    Integer i = 5;\n"
                +"    int k = i;\n"
                +"    //@ assert k == 5 ;\n"
                +"  }\n"
                
                +"  \n"
                +"  public void m1bad() {\n"
                +"    Integer i = 5;\n"
                +"    int k = i;\n"
                +"    //@ assert k == 6 ;\n"
                +"  }\n"
                
                +"  \n"
                +"  public void m1bad2() {\n"
                +"    Integer i = null;\n"
                +"    int k = i;\n"
                +"    //@ assert k == 6 ;\n"
                +"  }\n"
                

                +"  \n"
                +"  public void m2good() {\n"
                +"    Integer i = 5;\n"
                +"    //@ assert i != null ;\n"
                +"    //@ assert \\typeof(i) == \\type(Integer) ;\n" // Line 25
                +"  }\n"
                

                +"}"
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad2",13
                );
    }
    
    @Test
    public void testSimple2Static() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  static Integer i = 5;\n"
                +"  static int k = i;\n"
                +"  static { //@ assert k == 5; \n}\n"
                
                +"  static { Integer j = 6; int m = j; //@ assert m == 6; \n}\n"

                +"  static { Integer j = null; int m = j; \n}\n"

                +"}"
                );   // FIXME - should generate warnings here
    }
    
    @Test
    public void testSimple2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  Integer i = 5;\n"
                +"  int k = i;\n"
                +"  { //@ assert k == 5; \n}\n"
                
                +"  { Integer j = 6; int m = j; //@ assert m == 6; \n}\n"

                +"  { Integer j = null; int m = j; \n}\n"

                +"}",
                "/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method TestJava",31
                );
    }
    
    @Test
    public void testSwitch() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  public void m(int i) {;\n"
                +"  Integer k = i ; int m = 0;\n"
                +"  switch (k) {\n"
                
                +"    case 1: m = 1; break;\n"
                +"    case 2: m = i; break;\n"
                +"    default: m = i; break;\n"

                +"  } //@ assert m == i; \n"

                +"}}"
                );
    }
    
    @Test
    public void testSwitchShort() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  public void m(short i) {;\n"
                +"  Short k = i ; int m = 0;\n"
                +"  switch (k) {\n"
                
                +"    case 1: m = 1; break;\n"
                +"    case 2: m = i; break;\n"
                +"    default: m = i; break;\n"

                +"  } //@ assert m == i; \n"

                +"}}"
                );
    }
    
    @Test
    public void testSwitchByte() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  public void m(byte i) {;\n"
                +"  Byte k = i ; int m = 0;\n"
                +"  switch (k) {\n"
                
                +"    case 1: m = 1; break;\n"
                +"    case 2: m = i; break;\n"
                +"    default: m = i; break;\n"

                +"  } //@ assert m == i; \n"

                +"}}"
                );
    }
    
    @Test
    public void testSwitchNull() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  public void m(int i) {;\n"
                +"  Integer k = null ; int m = 0;\n"
                +"  switch (k) {\n"
                
                +"    case 1: m = 1; break;\n"
                +"    case 2: m = i; break;\n"
                +"    default: m = i; break;\n"

                +"  } //@ assert m == i; \n"

                +"}}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m",10
                );
    }
    
    @Test
    public void testBinary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                
                +"  public void m(int i) {\n"
                +"  Integer k = 6 ; int m = 1;\n"
                +"  int z = m + k; \n"
                +"  //@ assert z  == 7; \n"
                +"  z = k + m; \n"
                +"  //@ assert z == 8; \n"
                +"  } \n"

                +"  public void m1bad(int i) {\n"
                +"  Integer k = null; int m = 1;\n"
                +"  int z = m + k; \n"
                +"  } \n"

                +"  public void m2bad(int i) {\n"
                +"  Integer k = null; int m = 1;\n"
                +"  int z = k + m; \n"
                +"  } \n"

                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",7
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1bad",15
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (PossiblyNullUnbox) in method m2bad",11
                );
    }
    

}
