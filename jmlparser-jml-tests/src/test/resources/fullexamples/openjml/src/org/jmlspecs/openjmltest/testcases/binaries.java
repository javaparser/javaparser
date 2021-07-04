package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class binaries extends TCBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
        //main.addOptions("-jmldebug");
    }

    /** Tests that a system spec file is loaded from mock files - though this has no error reports to be sure it happened*/
    @Test
    public void testBinary() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{}\n public class File implements Serializable, Comparable<File> { \n//@model static public class TTT {} \n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
        );
    }

    /** Tests that a system spec file with an unmatched Java method is errored */
    @Test
    public void testBinary2() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File  implements Serializable, Comparable<File> { \n" +
                " public void m() {  }\n" +
                "//@model static class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.jml:3: The method java.io.File.m() is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class.",14
        );
    }
    
    /** Tests that a system spec file with an matched Java method is checked */
    @Test
    public void testBinary2a() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                " public void exists() { /*@ assert true; assume true; */ }\n" +
                "//@model static class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                // FIXME - different order in Java7 and Java8
                ,"/$A/java/io/File.jml:3: The return types of method java.io.File.exists() are different in the specification and java files: void vs. boolean",9
                ,"/$A/java/io/File.jml:3: The specification of the method java.io.File.exists() must not have a body",23
        );
    }
    
    /** Tests that model methods etc. in system spec files are actually checked */  // FIXME - not sure this should actually work - unlerss File is parsed by some other means, how would one know where VVV and TTT are
    @Test
    public void testBinary3() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ public static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "/*@ public invariant VVV.i; public invariant TTT.j; */ \n" +
                "//@model static class TTT { public static int j; } \n" +
                "}\n ");
        helpTCF("java/io/A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { /*@ assert java.io.VVV.i; assume java.io.File.TTT.j; */ }\n" +
                "}"
                ,"/java/io/A.java:3: incompatible types: int cannot be converted to boolean",42
                ,"/java/io/A.java:3: incompatible types: int cannot be converted to boolean",69
                ,"/$A/java/io/File.jml:3: incompatible types: int cannot be converted to boolean",25
                ,"/$A/java/io/File.jml:3: incompatible types: int cannot be converted to boolean",49
        );
    }

    /** Checks that a Java field in the spec file actually matches the binary; also various lookup tests */
    @Test
    public void testBinary4() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; \n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "  static public int j;\n" +
                "  //@ ghost static public int k; \n" +
                "}\n ");
        helpTCF("java/io/A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { boolean i = File.j; int ii = File.k; \n" +
                "     boolean q = File.separatorChar; \n" + 
                "     /*@ assert java.io.File.j; assume java.io.File.k; */ }\n" +
                "}"
                ,"/$A/java/io/File.jml:3: The field j is a Java field (neither ghost nor model) but does not match any fields in the corresponding Java class.",21
                ,"/java/io/A.java:3: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",36
                ,"/java/io/A.java:3: cannot find symbol\n  symbol:   variable k\n  location: class java.io.File",53
                ,"/java/io/A.java:4: incompatible types: char cannot be converted to boolean",22
                ,"/java/io/A.java:5: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",29
                ,"/java/io/A.java:5: incompatible types: int cannot be converted to boolean",52
        );
    }

    /** Checks that an extra Java class in a spec file is reported */
    @Test
    public void testBinary5() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; \n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "}\n" +
                "class Extra {}\n");
        helpTCF("java/io/A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.jml:4: This type declaration (java.io.Extra) is not matched by a binary class",1
        );
    }
}
