package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escstrings extends EscBase {
    
    public escstrings(String options, String solver) {
        super(options,solver);
    }
    
//    @Parameters
//    static public Collection<String[]> parameters() {
//        return EscBase.parameters();
//    }
    

    @Override
    public void setUp() throws Exception {
        super.setUp();
    }
    
    /** This String declaration and assignment */
    @Test
    public void testSimpleString() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m1(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s != null;\n"
                +"       //@ assert s == ss;\n"
                +"  }\n"
                
                +" public TestJava() { t = new TestJava(); }\n"
                +"}"
                );
    }
    
    /** Tests String equality  */
    @Test
    public void testStringEquals() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert s.equals(ss);\n"
                +"       //@ assert !s.equals(sss);\n"
                +"       //@ assert !sss.equals(ss);\n" // Null error
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",23
                
                );
    }
    
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs1a() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert s.equals(ss);\n"    // This would be true but we are not using any specs.
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs1() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       boolean b = s.equals(ss); //@ assert b;\n"     // This would be true but we are not using any specs.
                +"  }\n"
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",38
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs2() {
        main.addOptions("-internalSpecs=false");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       boolean b = !s.equals(sss); //@ assert b;\n"     // This would be true but we are not using any specs.
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m",40
                );
    }
   
    /** Tests String equality */
    @Test
    public void testStringEqualsNoSpecs3() {
        main.addOptions("-no-internalSpecs");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       /*@ nullable */ String sss = null;\n"
                +"       //@ assert  !sss.equals(ss);\n" // Null error
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",24
                );
    }
   
   
    /** Tests String concatenation - whether the result in Java is non-null. */
    @Test
    public void testStringConcat1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       String sss =  (s + ss);\n"
                +"       //@ assert sss != null;\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String concatenation - whether the result, computed in JML, is non-null*/
    @Test
    public void testStringConcat1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ reachable true;\n"
                +"       //@ assert (s + ss) != null;\n"
                +"  }\n"
                
                +" public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       String sss = s + ss;\n"
                +"       String s4 = s + ss;\n"
                +"       //@ assert sss.equals(s4);\n"
                +"  }\n"
                
                +"}" 
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assume s.length() + ss.length() <= Integer.MAX_VALUE;\n"
                +"       //@ assert (s+ss).equals(s+ss);\n"
                +"  }\n"
                
                +"}" 
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-method=m");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = (s + ss) == (s + ss); //@ assert b;\n" // Should not hold necessarily
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",46
                );
    }

    /** Tests String concatenation */
    @Test
    public void testStringConcat3a() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert (s + ss) == (s + ss);\n" // Should not hold necessarily
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt1q() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                                
                +"  //@ requires s.length() > 0; \n"
                +"  public void m(String s) {\n"
                +"       //@ assert s.charAt(0) == s.charAt(0);\n"
                +"  }\n"
                
                +"}"
                );
    }
    
    /** Tests String charAt operation */
    @Test
    public void testStringCharAt1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       //@ assert s.charAt(0) == s.charAt(0);\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m",27
                ,"$SPECS/specs/java/lang/String.jml:340: warning: Associated declaration",30
                ,optional("$SPECS/specs/java/lang/CharSequence.jml:70: warning: Precondition conjunct is false: 0 <= index < charArray.length",34)
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ requires s.length() > 0; \n"
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  //@ requires s.length() > 0;\n"
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // should not hold since s != ss
                +"  }\n"
                
                +"}"
                ,anyorder(
                        seq("/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m",12)
                        ,seq(seq("/tt/TestJava.java:6: warning: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m",43
                             ,"$SPECS/specs/java/lang/String.jml:340: warning: Associated declaration",30)
                             ,optional("$SPECS/specs/java/lang/CharSequence.jml:70: warning: Precondition conjunct is false: 0 <= index < charArray.length",34)
                            )
                                		
                        )
                );
    }

    /** Tests String charAt operation */
    @Test
    public void testStringCharAt3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  //@ requires s.length() > 0 && ss.length() > 0;\n"
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.charAt(0) == ss.charAt(0);\n"  // should not hold since s != ss
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1() {
    	main.addOptions("-method=m");
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       boolean b = s.length() >= 0; //@ assert b;\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       //@ assert s.length() >= 0;\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       boolean b = s.length() == ss.length(); //@ assert b;\n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength2a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s) {\n"
                +"       String ss = s;\n"
                +"       //@ assert s.length() == ss.length(); \n"
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       boolean b = s.length() == ss.length(); //@ assert b;\n" // should not hold
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",51
                );
    }

    /** Tests String length operation */
    @Test
    public void testStringLength3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void m(String s, String ss) {\n"
                +"       //@ assert s.length() == ss.length(); \n" // ERROR - not necessarily same length
                +"  }\n"
                
                +"  public TestJava() { t = new TestJava(); }"
                +"}"
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m",12
                );
    }

    // FIXME - also test interning

}