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
public class escprimitivetypes extends EscBase {

    public escprimitivetypes(String options, String solver) {
        super(options,solver);
    }
    
//    @Test
//    public void testIntset() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                
//                +"  //@ modifies \\everything;\n"
//                +"  public void m1(int i) {\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
//                +"    //@ ghost intset a;\n"
//                +"    //@ set a[ii] = false;\n"
//                +"    //@ ghost intset b = a;\n"
//                +"    //@ set a[ii] = true;\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == true;\n"
//                +"    //@ assert b[ii] == false;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testSet() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires o != oo;\n"
//                +"  public void m1(Object o,Object oo) {\n"
//                +"    //@ ghost set<Object> a;\n"
//                +"    //@ set a[o] = false;\n"
//                +"    //@ ghost set<Object> b = a;\n"
//                +"    //@ set a[o] = true;\n"
//                +"    //@ assert a[oo] == b[oo];\n"
//                +"    //@ assert a[o] == true;\n"
//                +"    //@ assert b[o] == false;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testIntmap() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, Object o, Object oo) {\n"
//                +"    //@ assume o != oo;\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
//                +"    //@ ghost intmap<Object> a;\n"
//                +"    //@ set a[ii] = oo;\n"
//                +"    //@ ghost intmap<Object> b = a;\n"
//                +"    //@ set a[ii] = o;\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == o;\n"
//                +"    //@ assert b[ii] == oo;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testArray() {
//        main.addOptions("-method=m1","-show");
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, Object o, Object oo) {\n"
//                +"    //@ assume o != oo;\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
//                +"    //@ ghost array<Object> a; \n"
//                +"    //@ set a[ii] = oo;\n"
//                +"    //@ ghost array<Object> b = a;\n"
//                +"    //@ set a[ii] = o;\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == o;\n"
//                +"    //@ assert b[ii] == oo;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testArrayPut() {
//        main.addOptions("-method=m1","-show");
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, Object o, Object oo) {\n"
//                +"    //@ assume o != oo;\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2;\n"
//                +"    //@ ghost array<Object> a; \n"
//                +"    //@ set a = a.put(ii,oo);\n"
//                +"    //@ ghost array<Object> b = a;\n"
//                +"    //@ set a = a.put(ii,o);\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == o;\n"
//                +"    //@ assert b[ii] == oo;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//
//    @Test
//    public void testseq() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, Object o, Object oo) {\n"
//                +"    //@ assume o != oo;\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
//                +"    //@ ghost seq<Object> a;\n"
//                +"    //@ set a[ii] = oo;\n"
//                +"    //@ ghost seq<Object> b = a;\n"
//                +"    //@ set a[ii] = o;\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == o;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testseqPut() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, Object o, Object oo) {\n"
//                +"    //@ assume o != oo;\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
//                +"    //@ ghost seq<Object> a;\n"
//                +"    //@ set a = a.put(ii,oo);\n"
//                +"    //@ ghost seq<Object> b = a;\n"
//                +"    //@ set a = a.put(ii,o);\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == o;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testmap() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(Object o, Object oo, Object ooo) {\n"
//                +"    //@ assume oo != ooo;\n"
//                +"    //@ ghost map<Object,Object> a;\n"
//                +"    //@ set a[oo] = ooo;\n"
//                +"    //@ ghost map<Object,Object> b = a;\n"
//                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
//                +"    //@ set a[oo] = o;\n"
//                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
//                +"    //@ assert a.get(oo) == o;\n"
//                +"    //@ assert b.get(oo) == ooo;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void testmapPut() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(Object o, Object oo, Object ooo) {\n"
//                +"    //@ assume oo != ooo;\n"
//                +"    //@ ghost map<Object,Object> a;\n"
//                +"    //@ set a = a.put(oo,o);\n"
//                +"    //@ ghost map<Object,Object> b = a;\n"
//                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
//                +"    //@ set a = a.put(oo,oo);\n"
//                +"    //@ assert a.get(ooo) == b.get(ooo);\n"
//                +"    //@ assert a.get(oo) == oo;\n"
//                +"    //@ assert b.get(oo) == o;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void teststring() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, char c, char cc) {\n"
//                +"    //@ assume c != cc; \n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
//                +"    //@ ghost string a;\n"
//                +"    //@ set a[ii] = cc;\n"
//                +"    //@ ghost string b = a;\n"
//                +"    //@ set a[ii] = c;\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == c;\n"
//                +"    //@ assert b[ii] == cc;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    @Test
//    public void teststringPut() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, char c, char cc) {\n"
//                +"    //@ assume c != cc; \n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; assume ii >= 0; \n"
//                +"    //@ ghost string a;\n"
//                +"    //@ set a = a.put(ii,cc);\n"
//                +"    //@ ghost string b = a;\n"
//                +"    //@ set a = a.put(ii,c);\n"
//                +"    //@ assert a[ii+1] == b[ii+1];\n"
//                +"    //@ assert a[ii] == c;\n"
//                +"    //@ assert b[ii] == cc;\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//    
//    
//    @Test
//    public void testJavaArray() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, boolean[] a) {\n"
//                +"    //@ assume a.length > 10 && i > 0 && i < a.length;\n"
//                +"    boolean bb = a[i];\n"
//                +"    int len = a.length;\n"
//                +"    a[0] = false;\n"
//                +"    boolean[] b = a;\n"
//                +"    a[i] = true;\n"
//                +"    //@ assert !b[0] && b[i];\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//
//    @Test
//    public void testJavaArray1() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, boolean[] a) {\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; \n"
//                +"    //@ assume 0 <= ii && ii < a.length;\n"
//                +"    //@ ghost boolean b = a[ii];\n"
//                +"  }\n"
//                +"}"
//                );
//    }
//
//    @Test
//    public void testJavaArray1a() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, boolean[] a) {\n"
//                +"    //@ ghost \\bigint ii = i; set ii = ii*2; \n"
//                +"    //@ assume 0 <= ii;\n"
//                +"    //@ ghost boolean b = a[ii];\n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",28
//                );
//    }
//
//    @Test
//    public void testJavaArray2() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, boolean[] a) {\n"
//                +"    //@ assume i < a.length; \n"
//                +"    boolean bb = a[i];\n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1",19
//                );
//    }
//
//
//    @Test
//    public void testJavaArray3() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1(int i, boolean[] a) {\n"
//                +"    //@ assume i >= 0; \n"
//                +"    boolean bb = a[i];\n"
//                +"  }\n"
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",19
//                );
//    }
    
    @Test
    public void testX() {
        main.addOptions("-method=m1");
        helpTCX("tt.TestJava","package tt; \n"
                                +"public class TestJava { \n"
                                
                                +"  public void m1(Object o) {\n"
                                +"    //@ ghost array<Object> a; \n"
                                +"    //@ set a[3] = o;\n"
                                +"  }\n"
                                +"}"
                                );
        
    }

}
