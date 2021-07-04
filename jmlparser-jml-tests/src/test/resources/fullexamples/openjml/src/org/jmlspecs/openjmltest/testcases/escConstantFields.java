package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escConstantFields extends EscBase {

    public escConstantFields(String options, String solver) {
        super(options,solver);
    }
    
    @Test
    public void testBasic() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = 1;\n"
                +"  public final static int J = 1 + I;\n"
                +"  //@ ensures J == 2;\n"
                +"  public TestJava() {  }\n"
                +"  //@ ensures J == 2;\n"
                +"  public void m() {}\n"
                +"  //@ ensures J == 2;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testGhost() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ ghost public final static int I = 1;\n"
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ ensures J == 2;\n"
                +"  public TestJava() {  }\n"
                +"  //@ ensures J == 2;\n"
                +"  public void m() {}\n"
                +"  //@ ensures J == 2;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFields() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = 1;\n"
                +"  //@ ghost public final static int J = 1 + I;\n"
                // Does not need the invariant
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // final variables are not affected by assignable \everything
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // final variables are not affected by assignable \everything
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotFinal() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public static int I = 1;\n"
                +"  //@ ghost public static int J = 1 + I;\n"
                +"  //@ public static invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // reestablishes the static invariant
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  //@ ensures J == 2;\n"
                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // reestablishes the static invariant
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotConstant() {
        main.addOptions("-no-staticInitWarning");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = z();\n"  // FIXME - static initialization check should fail
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ public static invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // final variables not subject to \everything
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // final variables not subject to \everything
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testFieldsNotConstantNoInvariant() {
        main.addOptions("-no-staticInitWarning");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = z();\n"  
                +"  //@ ghost public final static int J = 1 + z();\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n" // Fails since we don't have a static invariant
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n" // Fails since we don't have a static invariant
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"  //@ ensures \\result == 10;\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method TestJava",10
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testFieldsNotConstantWithHelper() {
        main.addOptions("-no-staticInitWarning");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final static int I = z();\n"
                +"  //@ ghost public final static int J = 1 + I;\n"
                +"  //@ public static invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // OK - fields are final
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n" // OK - fields are final
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"  /*@ helper */ static private int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFields() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = 1;\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n"  // OK - fields are final
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // OK - fields are final
                +"     //@ assert I == 1 && J == 2;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = 1;\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                // Does not need the invariant
                
                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // does not reestablish instance invariants
                +"     //@ assert I == 1 && J == 2;\n" // but OK because final constant fields are not modified by \everything
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n"
                +"     n();\n" // does not reestablish instance invariants
                +"     //@ assert I == 1 && J == 2;\n" // but OK because final fields are not modified by \everything
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotFinal() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int I = 1;\n"
                +"  //@ ghost public int J = 1 + I;\n"
                +"  //@ public invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n" // OK
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Should be OK because of invariant on n()
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Should be OK because of invariant on n()
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"   // FIXME _ why does this reestablish invariant?
                +"  public void n() {}\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotFinalS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public int I = 1;\n"
                +"  //@ ghost public int J = 1 + I;\n"
                +"  //@ public invariant I == 1 && J == 2;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 1 && J == 2;\n" // OK
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Fails because n is static and so does not establish the invariant
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 1 && J == 2;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 1 && J == 2;\n" // Fails because n is static and so does not establish the invariant
                +"  }\n"
                
                +"  //@ public normal_behavior assignable \\everything;\n"
                +"  static public void n() {}\n"   // FIXME _ why does this proove?
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method TestJava",10
                );
    }

    @Test
    public void testIFieldsNotConstant() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n" // FIXME - check that this is required

                +"  public TestJava() { \n"  // Default is assignable \everything, when not pure
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because of invariant on n()
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because of invariant on n()
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"   
                
                +"  //@ public normal_behavior ensures \\result == 10;\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotConstantS() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because final fields are not modified
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n" // OK because of invariant
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n" // Should be OK because final fields are not modified
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  static public void n() {}\n"
                
                +"  //@ public normal_behavior ensures \\result == 10;\n"
                +"  static public int z() { return 10; }\n"
                +"}"
                );
    }

    @Test
    public void testIFieldsNotConstantWithHelper() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public final int I = z();\n"
                +"  //@ ghost public final int J = 1 + I;\n"
                +"  //@ public invariant I == 10 && J == 11;\n"

                +"  public TestJava() { \n"   // Default is assignable everything, when not pure
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"

                +"  public void m() {\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"     n();\n"
                +"     //@ assert I == 10 && J == 11;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void n() {}\n"
                
                +"  //@ private normal_behavior ensures \\result == 10;\n"
                +"  /*@ helper */ static private int z() { return 10; }\n"
                +"}"
                );
    }

    @Test // initialized static final in another class, no invariants
    public void testConstants() {
        helpTCX("tt.TestJava","package tt; \n"
                +" class H { \n"
                +"   final public static int CON1 = 50;\n"
                +"   final public static int CON2 = 1 + CON1;\n"
                +"   final public static int CON3 = Integer.MAX_VALUE;\n"
                +" }\n"
                +"public class TestJava { \n"

                +"  public TestJava() {\n"
                +"    //@ assert H.CON1 == 50 ;\n"
                +"    //@ assert H.CON2 == 51 ;\n"
                +"    //@ assert H.CON2 == H.CON1 + 1 ;\n"
                +"    //@ assert H.CON3 == 0x7fffffff ;\n"
                +"    meverything();\n"
                +"    //@ assert H.CON1 == 50 ;\n"
                +"    //@ assert H.CON2 == 51 ;\n"
                +"    //@ assert H.CON2 == H.CON1 + 1 ;\n"
                +"    //@ assert H.CON3 == 0x7fffffff ;\n"
                +"  }\n"

                +"  \n"
                +"  public void m1() {\n"
                +"    //@ assert H.CON1 == 50 ;\n"
                +"    //@ assert H.CON2 == 51 ;\n"
                +"    //@ assert H.CON2 == H.CON1 + 1 ;\n"
                +"    //@ assert H.CON3 == 0x7fffffff ;\n"
                +"    meverything();\n"
                +"    //@ assert H.CON1 == 50 ;\n"
                +"    //@ assert H.CON2 == 51 ;\n"
                +"    //@ assert H.CON2 == H.CON1 + 1 ;\n"
                +"    //@ assert H.CON3 == 0x7fffffff ;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything;\n"
                +"  public void meverything() {\n"
                +"  }\n"
                
               
                +"}"
                );
    }

   }
