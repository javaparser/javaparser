package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class namelookup extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    @Test
    public void testLookup() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   //@ invariant k;\n" +
                "   //@ requires k;\n" +
                "   void m(double k) {}\n" +
                "}",
        "/A.java:3: incompatible types: double cannot be converted to boolean",17,
        "/A.java:2: incompatible types: int cannot be converted to boolean",18
        );
    }

    @Test
    public void testLookup2() {
        helpTCF("A.java",
                " public class A { int k; float d; \n" +
                "   //@ constraint \\old(k); constraint \\old(d);\n" +
                "   void m(double d) {\n" +
                "        //@ assert k;\n" +
                "        double k;\n" +
                "        //@ assert k;\n" +
                "        //@ assert \\old(k);\n" + 
                "        //@ assert \\old(d);\n" + 
                "   }\n" +
                "}",
        "/A.java:4: incompatible types: int cannot be converted to boolean",20,
        "/A.java:6: incompatible types: double cannot be converted to boolean",20,
        "/A.java:7: incompatible types: int cannot be converted to boolean",24,
        "/A.java:8: incompatible types: double cannot be converted to boolean",24,
        "/A.java:2: incompatible types: int cannot be converted to boolean",23, // FIXME - should these be errors because the k, d in scope does not exist in the pre-state?
        "/A.java:2: incompatible types: float cannot be converted to boolean",43
        );
    }

    @Test
    public void testLookup3() {
        helpTCF("A.java",
                " public class A { int k; Object o; \n" +
                "   void m() {\n" +
                "      //@ ghost Object k;\n" +
                "      boolean b = k == null;\n" +  // ERROR - k is Java variable with int type
                "      //@ assert k == 1;\n" + // ERROR - k is Object
                "      //@ assert k == null;\n" + // OK
                "      boolean bb = k == o;\n" + // ERROR - k is int
                "      boolean bbb = k == null;\n" +  // ERROR
                "   }\n" +
                "}",
        "/A.java:4: incomparable types: int and <nulltype>",21,
        "/A.java:5: incomparable types: java.lang.Object and int",20,
        "/A.java:7: incomparable types: int and java.lang.Object",22,
        "/A.java:8: incomparable types: int and <nulltype>",23);
    }

    @Test
    public void testDupField() {
        helpTCF("A.java",
                " class A { //@ ghost int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k) {}\n" +
                "}",
        "/A.java:2: variable k is already defined in class A",21
        );
    }

    @Test
    public void testDupField1() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   double k;\n" +
                "   void m(double k) {}\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: This specification declaration of field k has the same name as a previous field declaration",11
        ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",16
        ,"/$A/A.jml:3: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1b() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   int k;\n" +
                "   void m(double k) {}\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: This specification declaration of field k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",16
        ,"/$A/A.jml:3: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1a() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k);\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: variable k is already defined in class A",21

        );
    }

    @Test
    public void testDupField2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k) {}\n" +
                "}"
                //,"/A.java:2: This specification declaration of field k has the same name as a previous field declaration", 21
                //,"/A.java:1: Associated declaration: /A.java:2: ", 16
                ,"/A.java:2: variable k is already defined in class A",21
                );
    }

    @Test
    public void testDupVar() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   void m(double d) {\n" +
                "      int d;\n" +
                "   }\n" +
                "}",
        "/A.java:3: variable d is already defined in method m(double)",11);
    }

    @Test
    public void testDupVar2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   void m(double d) {\n" +
                "      //@ ghost int d;\n" +
                "   }\n" +
                "}",
        "/A.java:3: variable d is already defined in method m(double)",21);
    }

    @Test
    public void testGhostField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ ghost double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" +
                "      //@ assert k;\n" +
                "   }\n" +
                "}",
        "/A.java:4: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: incompatible types: double cannot be converted to boolean",18);
    }

    @Test
    public void testModelField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ model double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" +
                "      //@ assert k;\n" +
                "   }\n" +
                "}",
        "/A.java:4: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: incompatible types: double cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ model pure double k() { return 0; }\n" +
                "   void m() {\n" +
                "      boolean kk = k();\n" +
                "      //@ assert k();\n" +
                "   }\n" +
                "}",
        "/A.java:4: cannot find symbol\n  symbol:   method k()\n  location: class A", 20,
        "/A.java:5: incompatible types: double cannot be converted to boolean",19);
    }

    @Test
    public void testModelMethod2() {
        helpTCF("A.java",
                " class A {   int k() { return 0; }\n" +
                "   //@ model double k() { return 1; }\n" +
                "   void m() {\n" +
                "      boolean kk = k();\n" +
                "   }\n" +
                "}"
		        ,"/A.java:2: method k() is already defined in class A",21
		        ,"/A.java:4: incompatible types: int cannot be converted to boolean", 21
        );
    }

    @Test
    public void testModelMethod3() {
        helpTCF("A.java",
                " class A { /*@pure*/  int k(int i) { return 0; }\n" +
                "   //@ model pure double k(boolean d) { return 0; }\n" +
                "   //@ requires k(true); \n" +
                "   //@ requires k(0); \n" +
                "   void m() {\n" +
                "   }\n" +
                "}",
        "/A.java:3: incompatible types: double cannot be converted to boolean", 18,
        "/A.java:4: incompatible types: int cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod4() {
        helpTCF("A.java",
                " class A {   static /*@pure*/int k(int i) { return 0; }\n" +
                "   static class B {\n" +
                "      //@ model pure static double k(int i) { return 0; }\n" +
                "      boolean b = k(0);\n" +
                "      //@ requires k(0); \n" +
                "      void m() {\n" +
                "         boolean kk = k(0);\n" +
                "         //@ assume k(0);\n" +
                "      }\n" +
                "   }\n" +
                "}"
        ,"/A.java:4: incompatible types: int cannot be converted to boolean", 20
        ,"/A.java:5: incompatible types: double cannot be converted to boolean", 21
        ,"/A.java:7: incompatible types: int cannot be converted to boolean", 24
        ,"/A.java:8: incompatible types: double cannot be converted to boolean", 22
        );
    }

    /** No body for model method is OK */
    @Test
    public void testModelMethod5() {
        helpTCF("A.java",
                " class A {   \n" +
                "      //@ model pure static double k(int i);\n" +
                "      //@ requires k(0); \n" +
                "      void m() {\n" +
                "         //@ assume k(0);\n" +
                "      }\n" +
                "}"
        ,"/A.java:3: incompatible types: double cannot be converted to boolean", 21
        ,"/A.java:5: incompatible types: double cannot be converted to boolean", 22
        );
    }

    @Test
    public void testModelClass() {
        helpTCF("A.java",
                " public class A {   \n" +
                "   static class AA {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m() {\n" +
                "         boolean kk = B.i;\n" +
                "         //@ assert B.i;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                " class B { static int i; }  \n" +
                ""
        ,"/A.java:7: incompatible types: int cannot be converted to boolean",24 
        ,"/A.java:8: incompatible types: double cannot be converted to boolean",22
        );
    }
 
    @Test
    public void testModelClass2() {
        helpTCF("A.java",
                " class A {   \n" +
                "   static class AA {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m() {\n" +
                "         boolean kk = B.i;\n" +
                "         //@ assert B.i;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                ""
        ,"/A.java:4: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
        ,"/A.java:7: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
        ,"/A.java:8: incompatible types: double cannot be converted to boolean",22
            );
    }

    @Test
    public void testModelClass3() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "   static class AA { \n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m(); \n" +
                "         \n" +
                "         \n" +
                "      \n" +
                "   }\n" +
                "   static class AA {\n" +
                "   }\n" +
                "   static class BB {\n" +
                "   }\n" +
                "}\n" +
                "class A {}\n" +
                "class B {}\n" +
                ""
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "   static class AA { \n" +
                "      B b;\n" + // ERROR - AA.B visible only in specs
                "      void m() {\n" +
                "         boolean kk = B.i;\n" + // ERROR - AA.B visible only in specs
                "         //@ assert B.i;\n" + // OK, but wrong type
                "      }\n" +
                "   }\n" +
                "}\n"

                // Change in output for Java8
                ,"/$A/A.jml:16: duplicate class: A",1
//       ,"/$A/A.jml:16: This specification declaration of type A has the same name as a previous JML type declaration",1
//       ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:16: ",8
       ,"/$A/A.jml:17: This specification declaration of type B does not match any Java type declaration in /A.java",1
       ,"/$A/A.jml:11: duplicate class: AA",11
//       ,"/$A/A.jml:11: This specification declaration of type AA has the same name as a previous JML type declaration",11
//       ,"/$A/A.jml:2: Associated declaration: /$A/A.jml:11: ",11
       ,"/$A/A.jml:13: This specification declaration of type BB does not match any Java type declaration in /A.java",11
       ,"/A.java:3: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
 //      ,"/$A/A.jml:4: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
        ,"/A.java:5: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
        ,"/A.java:6: incompatible types: double cannot be converted to boolean",22
        );
    }
 
    @Test
    public void testToplevelModel() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "}\n" +
                "//@ model class A {}\n" +
                "//@ model class B {}\n" +
                "//@ model class B {}\n" +
                "/*@ model class C {}*/\n" +
                " class D {}"
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "}\n" +
                ""
        // Java 8
        ,"/$A/A.jml:3: duplicate class: A", 11
        ,"/$A/A.jml:5: This specification declaration of type B has the same name as a previous JML type declaration", 11
        ,"/$A/A.jml:4: Associated declaration: /$A/A.jml:5: ",11
        ,"/$A/A.jml:7: This specification declaration of type D does not match any Java type declaration in /A.java",2

        // Java 7
//        ,"/$A/A.jml:7: This specification declaration of type D does not match any Java type declaration in /A.java",2
//        ,"/$A/A.jml:3: This specification declaration of type A has the same name as a previous JML type declaration",11
//        ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:3: ",8
//        ,"/$A/A.jml:5: duplicate class: B",11   // FIXME - OpenJML reports wrong location

        );
    }
 
}
