package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typechecking extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        useSystemSpecs = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
        //main.addOptions("-jmldebug");
    }

    /** Test something very simple with no errors*/
    @Test public void testSomeJava() {
//    	main.addOptions("-verbose");
        helpTC("import org.jmlspecs.lang.JMLDataGroup; class A { public A(){} }");
    }

    /** Test something very simple with no errors*/
    @Test public void testSomeJavaB() {
        helpTC(" class A {}");
    }

    /** Test a particular error*/
    @Test public void testSomeJavaBrace() {
        helpTC(" class A {} }"
        ,"/TEST.java:1: class, interface, or enum expected",13,12,12,12 // FIXME - end position may not be useful - should be 13?
        );
    }

    /** Test scanning something very simple */
    @Test public void testSomeJava2() {
        helpTC(" class A { int k = true; }",
                "/TEST.java:1: incompatible types: boolean cannot be converted to int",20);
    }

    /** Test scanning something very simple */
    @Test public void testSomeJML() {
        helpTC(" class A { int k; boolean b; void m() { \n//@ assert k;\n}}",
                "/TEST.java:2: incompatible types: int cannot be converted to boolean",12);
    }

    @Test public void testTypeArgs() {
        helpTC(" class A { int k; boolean b; <T> int mm() {} void m() { int t = this.<Integer>mm(); \n//@ assert <Object>\\old(k);\n}}"
                ,"/TEST.java:2: illegal start of expression",13
                );
    }

    @Test public void testAlso0() {
        helpTC(" class B { void m() {} } class A extends B { /*@ also requires true; */ void m() {}  /*@ requires true; */ void n() {}}"
                );
    }

    @Test public void testAlso1() {
    	expectedExit = 0;
        helpTC(" class B { void m() {} } class A extends B { /*@ requires true; */ void m() {} /*@ also requires true; */ void n() {}}"
                ,"/TEST.java:1: warning: Method m overrides parent class methods and so its specification should begin with 'also'",50
                ,"/TEST.java:1: warning: Method n does not override parent class methods and so its specification may not begin with 'also'",89
                );
    }

    @Test public void testAlso0I() {
        helpTC(" interface B { void m(); } class A implements B { /*@ also requires true; */ public void m() {}  /*@ requires true; */ void n() {}}"
                );
    }

    @Test public void testAlso1I() {
    	expectedExit = 0;
        helpTC(" interface B { void m(); } class A implements B { /*@ public normal_behavior requires true; */ public void m() {} /*@ also requires true; */ void n() {}}"
                ,"/TEST.java:1: warning: Method m overrides parent class methods and so its specification should begin with 'also'",62
                ,"/TEST.java:1: warning: Method n does not override parent class methods and so its specification may not begin with 'also'",124
                );
    }

    @Test public void testAlso0II() {
        helpTC(" interface B { void m(); } interface A extends B { /*@ also requires true; */ public void m();  /*@ requires true; */ void n();}"
                );
    }

    @Test public void testAlso1II() {
    	expectedExit = 0;
        helpTC(" interface B { void m(); } interface A extends B { /*@ requires true; */ void m(); /*@ also requires true; */ void n();}"
                ,"/TEST.java:1: warning: Method m overrides parent class methods and so its specification should begin with 'also'",56
                ,"/TEST.java:1: warning: Method n does not override parent class methods and so its specification may not begin with 'also'",93
                );
    }

    @Test public void testAlsoObject() {
    	expectedExit = 0;
        helpTC("  interface A { /*@ also public normal_behavior requires true; */ String toString();}"
                );
    }

    @Test public void testAlsoObjectBad() {
    	expectedExit = 0;
        helpTC("  interface A { /*@ public normal_behavior requires true; */ String toString();}"
                ,"/TEST.java:1: warning: Method toString overrides parent class methods and so its specification should begin with 'also'",28
                );
    }

    @Test public void testOld1() {
        helpTC(" class A { int k; boolean b; void m() { \n//@ assert \\old;\n}}",
                "/TEST.java:2: A \\old expression must have an argument list",12);
    }

    @Test public void testOld2() {
        helpTC(" class A { int k; boolean b; void m() { \n//@ assert \\old();\n}}",
                "/TEST.java:2: A \\old expression expects just 1 or 2 arguments, not 0",16);
    }

    @Test public void testOld2a() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\pre();\n}}",
                "/A.java:2: A \\pre expression expects just 1 argument, not 0",16);
    }

    @Test public void testOld3() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(k);\n}}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",16);
    }

    @Test public void testOld4() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b);\n}}");
    }

    @Test public void testOld5() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\pre(b,k);\n}}",
                "/A.java:2: A \\pre expression expects just 1 argument, not 2",16
                ,"/A.java:2: There is no label named k",19);
    }

    @Test public void testOld6() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b,5);\n}}",
                "/A.java:2: The second argument of an \\old expression must be a simple identifier that is a label",19);
    }

    @Test public void testOld7() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b,k);\n}}"
                ,"/A.java:2: There is no label named k",19);
    }

    @Test public void testOld8() {
        helpTCF("A.java"," class A { int k; boolean b; //@ requires \\old(b); \n void m() { }}",
                "/A.java:1: A \\old token with no label may not be present in a requires clause",48);
    }

    @Test public void testOld9() {
        helpTCF("A.java"," class A { int k; boolean b; //@ ensures \\old(b,k); \n void m() { }}",
                "/A.java:1: A \\old token with a label may not be present in a ensures clause",47);
    }

    @Test public void testOld10() {
        helpTCF("A.java"," class A { int k; boolean b; //@ requires \\pre(b); \n void m() { }}",
                "/A.java:1: A \\pre token may not be present in a requires clause",48);
    }

    @Test public void testOld11() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n k: k=1;\n //@ assert \\old(b,k);\n}}"
                );
    }

    @Test public void testOld12() {
        helpTCF("A.java"," class A { boolean b; void m() { \n k: {};\n boolean bb = false; //@ assert \\old(bb) && \\old(bb,k);\n}}"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable bb\n  location: class A",38
                ,"/A.java:3: cannot find symbol\n  symbol:   variable bb\n  location: class A",50
                );
    }

    @Test public void testOld13() {
        helpTCF("A.java"," class A { boolean b; void m() { \n k: {};\n //@ assert \\old(b,k);\n}}"
                );
    }

    @Test public void testMax() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(\\lockset);\n}}",
                "/A.java:2: incompatible types: java.lang.Object cannot be converted to boolean",16);
    }

    @Test public void testMax1() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max;\n}}",
                "/A.java:2: illegal start of type",16);
    }

    @Test public void testMax2() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max();\n}}",
                "/A.java:2: A \\max expression expects just 1 argument, not 0",16);
    }

    @Test public void testMax3() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(k);\n}}",
                "/A.java:2: A \\max function expects an argument of type org.jmlspecs.lang.JMLSetType<E> rather than int",17,
                "/A.java:2: incompatible types: java.lang.Object cannot be converted to boolean",16
                );
    }

    @Test public void testMax5() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(b,k);\n}}",
                "/A.java:2: A \\max expression expects just 1 argument, not 2",16,
                "/A.java:2: A \\max function expects an argument of type org.jmlspecs.lang.JMLSetType<E> rather than boolean",17,
                "/A.java:2: incompatible types: java.lang.Object cannot be converted to boolean",16);
    }

    @Test public void testInvariantFor1() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(i);\n}}"
        		);
    }

    @Test public void testInvariantFor2() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(k);\n}}"
        		,"/A.java:2: The argument of \\invariant_for must be of reference type", 27
        		);
    }

    @Test public void testInvariantFor3() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(A);\n}}"
        		);
    }

    @Test public void testInvariantFor4() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for();\n}}"
        		);
    }

    @Test public void testInvariantFor5() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
        		,"/A.java:2: The argument of \\invariant_for must be of reference type", 35
        		);
    }

    @Test public void testInvariantFor6() {
    	main.addOptions("-lang=jml");
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
        		,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The \\count construct is an OpenJML extension to JML and not allowed under -lang=jml",37
        		,"/A.java:2: A \\invariant_for expression expects just 1 argument, not 2", 26
        		,"/A.java:2: The argument of \\invariant_for must be of reference type", 27
        		,"/A.java:2: The argument of \\invariant_for must be of reference type", 35
        		);
    }

    @Test public void testInvariantFor6a() {
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
        		,"/A.java:2: The argument of \\invariant_for must be of reference type", 35
        		);
    }

    @Test public void testInvariantFor7() {
    	main.addOptions("-lang=jml");
        helpTCF("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for();\n}}"
        		,"$SPECS/specs/java/util/stream/Stream.jml:$STRL: warning: The \\count construct is an OpenJML extension to JML and not allowed under -lang=jml",37
        		,"/A.java:2: A \\invariant_for expression expects just 1 argument, not 0", 26
        		);
    }


    @Test public void testType() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(A,k);\n}}"
                ,"/A.java:2: More than one argument or otherwise ill-formed type expression as argument of \\type",19
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType2() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type();\n}}"
                ,"/A.java:2: illegal start of type",18
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType3() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(b);\n}}"
                ,"/A.java:2: cannot find symbol\n  symbol:   class b\n  location: class A",18
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType4() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(true);\n}}"
                ,"/A.java:2: illegal start of type",18
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType5() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(int);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType6() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(int[][]);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType7() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(Object);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType8() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(java.lang.Object);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType9() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(java.lang.Object[][]);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                            );
    }

    @Test public void testType10() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(A);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType11() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(void);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType12() {
        helpTCF("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(Void);\n}}"
                ,"/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testTypeof() {
        helpTCF("A.java"," class A { int k; Boolean b; void m() { \n//@ assert \\typeof(b);\n}}",
                "/A.java:2: incompatible types: \\TYPE cannot be converted to boolean",19);
    }

    @Test public void testResult() {
        helpTC(" class A { int k; Boolean b; void m() { \n//@ assert \\result;\n}}"
                ,"/TEST.java:2: A \\result expression may not be used in the specification of a method that returns void",13
                ,"/TEST.java:2: A \\result expression may not be in a assert clause",13
                );
    }

    @Test public void testResult3() {
        helpTCF("A.java"," public class A { int k; Boolean b;\n //@ ensures \\result;\n void m() { \n}}",
                "/A.java:2: A \\result expression may not be used in the specification of a method that returns void",15);
    }

    @Test public void testResult4() {
        helpTC(" class A { int k; Boolean b;\n //@ assert \\result;\n void m() { \n}}",
                "/TEST.java:2: The token assert is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",6);
    }

    @Test public void testResult2() {
        String s = " class A { int k; Boolean b;\n/*@ ensures \\result == 1; */\nboolean m() { \n return true;\n}}";
        helpTCF("A.java",s,
                "/A.java:2: incomparable types: boolean and int",21);
    }

    @Test public void testResult5() {
        String s = " class A { int k; Boolean b;\n/*@ ensures \\result == 1; */\n void m() { }}";
        helpTCF("A.java",s,
                "/A.java:2: A \\result expression may not be used in the specification of a method that returns void",14);
    }

    /** Tests an input that gave bugs once before */
    @Test public void testMisc1() {
        helpTC(" class A { /*@ ensures \\result     ; */\nboolean m() { \n//@ return true;\n}}"
                ,"/TEST.java:3: Expected a declaration or a JML construct inside the JML annotation here", 5
        );
    }
    
    @Test public void testMisc1b() {
        helpTC(" class A { /*@ ensures \\result     ; */\nboolean m() { \n//@ int t;\n}}"
                ,"/TEST.java:3: A local declaration within a JML annotation must be ghost", 9 // FIXME - better position
        );
    }
    
    @Test public void testJmlTypes() {
        helpTCF("A.java","public class A {  int i; /*@ ghost \\TYPE t; */ } ");  //OK
    }

    @Test public void testJmlTypes0() {
        helpTCF("A.java","public class A {  int i,j; /*@ ghost \\TYPE t,tt; */ } "); //OK
    }

    @Test public void testJmlTypes1() {
        helpTCF("A.java","public class A {  /*@ ghost \\bigint i; model \\real r; ghost \\TYPE t; */ } "); //OK
    }

    /** Missing model or ghost modifier */
    @Test public void testJmlTypes2() {
        helpTCF("A.java","public class A {  int i; /*@  \\TYPE t; */ } ",
                "/A.java:1: A declaration within a JML annotation must be either ghost or model",37);
    }

    /** Wrong position model or ghost modifier */
    @Test public void testJmlTypes3() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A {  @Ghost int i; } ",
                "/A.java:1: A Java declaration (not within a JML annotation) may not be either ghost or model",64);
    }

    @Test public void testJmlTypes4() {
        helpTCF("A.java","import org.jmlspecs.annotation.*; public class A {  /*@ @Ghost int i; */ } ");  //OK
    }
    @Test public void testSubtype() { // OK
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */Class c;\n//@ensures t <: t;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2() { // OK
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class c;\n//@ensures c <: c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2a() { // OK
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures c <: c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2b() { // OK
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<? extends Object> c;\n//@ensures c <: c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype3() { // OK
        expectedExit = 0;
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures t <: \\typeof(o);\nvoid m() {}}"
                );
    }
    
    @Test public void testSubtype4() { // OK
        expectedExit = 0;
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures o.getClass() <: Object.class;\nvoid m() {}}"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: getClass()",22
                );
    }
    
    @Test public void testSubtype5() {
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures JML.erasure(t) <: c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype6() {
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures t <: 5;\nvoid m() {}}",
                "/A.java:2: The type of the arguments of the subtype operator (<:) must be either \\TYPE or java.lang.Class, not int",17);
    }
    
    @Test public void testSubtype7() {
        helpTCF("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ensures true <: c;\nvoid m() {}}",
                "/A.java:2: The type of the arguments of the subtype operator (<:) must be either \\TYPE or java.lang.Class, not boolean",12);
    }
    
    @Test public void testErasure1() {
        helpTCF("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.lang.Integer);\n}"
                );
    }
    
    @Test public void testErasure2() {
        helpTCF("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.util.List);\n}"
                ,"/A.java:1: The argument of a \\type construct must be a fully parameterized type: java.util.List",53
                );
    }
    
    @Test public void testErasure3() {
        helpTCF("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.util.List<Integer>);\n}"
                );
    }
    
    @Test public void testErasure4() {
        helpTCF("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.lang.Integer));\n}"
                );
    }
    
    @Test public void testErasure5() {
        helpTCF("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.util.List));\n}"
                );
    }
    
    @Test public void testErasure6() {
        helpTCF("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.util.List<Integer>));\n}"
                );
    }
    
    @Test public void testMisplacedResult() {
        helpTCF("A.java","public class A {  \n//@requires \\result == 0;\n int m() {return 0;}}",
                "/A.java:2: A \\result expression may not be in a requires clause",14);
        
    }
    
    @Test public void testSetComp() {
        helpTCF("A.java","public class A {  \n java.util.Collection c; //@ invariant new JMLSetType { Integer i | c.contains(i) && i<10}; \n \n }"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: contains(java.lang.Object)",79  // FIXME
                ,"/A.java:2: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to boolean",55
		);
    }
    
    // Testing scopes in method specs
    @Test public void testSetCompA() {
        helpTCF("A.java","public class A {  \n java.util.Collection c; //@ requires new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: contains(java.lang.Object)",78 // FIXME
                ,"/A.java:2: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to boolean",54
                );
    }

    @Test public void testQuantifierA() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n //@ requires m( (\\exists int i; 0 < i && i <10; m(i)) ); \n/*@pure*/boolean m(int k) { return false; }\n }",
                "/A.java:3: incompatible types: boolean cannot be converted to int",18);
    }
  
    @Test public void testSetCompB() {
        helpTCF("A.java","public class A {  \n java.util.Collection c; //@ ghost int k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
                ,"/A.java:2: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to int",59
        );
    }

    @Test public void testSetCompB3() {
        helpTCF("A.java","public class A {  boolean p; \n java.util.Collection c; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && p<10}; \n void m() {} \n }"
                ,"/A.java:2: bad operand types for binary operator '<'\n  first type:  boolean\n  second type: int",94
        );
    }

    @Test public void testSetCompB2() {
        helpTCF("A.java","public class A {  \n java.util.Collection c; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
        );
    }

    @Test public void testQuantifierB() {
        helpTCF("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(int k) { return false; }\n }",
                "/A.java:2: incompatible types: boolean cannot be converted to int",27);
    }
  
    @Test public void testQuantifierB2() {
        helpTCF("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(boolean k) { return false; } boolean m(int p) { return false; }\n }"
                );
    }
  
    @Test public void testQuantifierB3() {
        helpTCF("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(boolean k) { return false; } \n }"
                ,"/A.java:2: incompatible types: int cannot be converted to boolean",61
                );
    }
  
    // Looking for a name in the outer scope
    @Test public void testQuantifierB4() {
        helpTCF("A.java","public class A { boolean p;  \n  //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(p)) ); \nboolean m(int k) { return false; } \n }"
                ,"/A.java:2: incompatible types: boolean cannot be converted to int",61
                );
    }
  
    // testing scopes in local initializers
    @Test public void testSetCompC() {
        helpTCF("A.java","public class A {  \n java.util.Collection c;  void m() { //@ ghost int k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                ,"/A.java:2: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to int",71
                );
    }

    @Test public void testSetCompC3() {
        helpTCF("A.java","public class A {  \n java.util.Collection c;  void m() { boolean p; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && p<10}; \n} \n }"
                ,"/A.java:2: bad operand types for binary operator '<'\n  first type:  boolean\n  second type: int",117
                );
    }

    @Test public void testSetCompC2() {
        helpTCF("A.java","public class A {  \n java.util.Collection c;  void m() { //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                );
    }

    @Test public void testQuantifierC() {
        helpTCF("A.java","public class A {  \n  boolean m(int k) { //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }",
                "/A.java:2: incompatible types: boolean cannot be converted to int",46
                );
    }
    
    @Test public void testQuantifierC2() {
        helpTCF("A.java","public class A {  \n  boolean m(int k) { //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }"
                );
    }
    
    @Test public void testQuantifierC3() {
        helpTCF("A.java","public class A {  \n  boolean m(int k) { boolean p ; //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(p)) ); \n return false; }\n }",
                "/A.java:2: incompatible types: boolean cannot be converted to int",92
                );
    }
    
    // testing scopes in JML statements
    @Test public void testSetCompD() {
        helpTCF("A.java","public class A {//@ ghost Object k;  \n java.util.Collection c;  void m() { //@ set k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                );
    }

    @Test public void testQuantifierD() {
        helpTCF("A.java","public class A { //@ ghost int j;\n  \n  boolean m(int k) { //@ set j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }",
                "/A.java:3: incompatible types: boolean cannot be converted to int",37);
    }
    
    @Test public void testQuantifier() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@pure*/ boolean m(int i) { return false; }\n//@ invariant m( (\\exists int i; 0 < i && i <10; m(i)) ); \n }",
                "/A.java:4: incompatible types: boolean cannot be converted to int",18);
    }
    
    @Test public void testQuantifier1() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@pure*/ boolean m(int i) { return false; }\n//@ invariant m( (\\forall int i; 0 < i && i <10; m(i)) ); \n }",
                "/A.java:4: incompatible types: boolean cannot be converted to int",18);
    }
    
    @Test public void testQuantifier2() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@pure*/ boolean m(int i) { return false; }\n//@ invariant (\\num_of int i; 0 < i && i <10; m(i)) ; \n }",
                "/A.java:4: incompatible types: int cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier3() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(int i) { return false; }\n//@ invariant (\\max long i; 0 < i && i <10; i) ; \n }",
                "/A.java:4: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier4() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(float i) { return false; }\n//@ invariant (\\sum long i; 0 < i && i <10; i) ; \n }",
                "/A.java:4: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier5() {
        helpTCF("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i,k; 0 < i && k <10; i) ; \n }",
                "/A.java:4: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier6() {
        helpTCF("A.java","public class A {  \n Object i; Object q = i; //@ ghost Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i; j; i) ; \n }",
                "/A.java:4: incompatible types: java.lang.Object cannot be converted to boolean",33,
                "/A.java:4: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier7() {
        helpTCF("A.java","public class A {  \n Object i; Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i; 0 < j && i <10; i) ; \n }",
                "/A.java:4: bad operand types for binary operator '<'\n  first type:  int\n  second type: java.lang.Object",35,
                "/A.java:4: incompatible types: long cannot be converted to boolean",16);
    }

    @Test public void testQuantifierInv() {
        helpTCF("A.java","public class A {  \n //@ invariant (\\exists int i; 0 < i && i <10;  i > -1) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > -1) ; \n void m() {}}"

                );
    }
    
    @Test public void testQuantifierInv1() {
        helpTCF("A.java","public class A { int m; static int s; \n //@ invariant (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > m) ; \n void m() {}}"
                ,"/A.java:3: non-static variable m cannot be referenced from a static context",60
                );
    }
    
    @Test public void testQuantifierInv2() {
        helpTCF("A.java","public class A { int m; static int s; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > s) ; \n void m() {}}"

                );
    }
    
    @Test public void testQuantifierInit() {
        helpTCF("A.java","public class A { int m; static int s; \n //@ ghost boolean b = (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ static ghost boolean bb = (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ requires b && bb;\n void m() {}}"
                ,"/A.java:3: non-static variable m cannot be referenced from a static context",69
                );
    }
    
    @Test public void testQuantifierInit1() {
        helpTCF("A.java","public class A { int m; static int s; \n //@ ghost boolean b = (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ static ghost boolean bb = (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ requires b && bb;\n void m() {}}"

                );
    }
    
    @Test public void testQuantifierReq() {
        helpTCF("A.java","public class A {  \n //@ requires (\\exists int i; 0 < i && i <10;  i > -1) ; \n  void m() {}}"

                );
    }
    
    @Test public void testQuantifierReq2() {
        helpTCF("A.java","public class A {  \n //@ requires (\\exists int i; 0 < i && i <10;  i > -1) ; \n  static void m() {}}"

                );
    }
    

    @Test public void testLet() {
        helpTCF("A.java","public class A { void m() { //@ assert (\\let int i = 0; i != 0); \n}}"
                );
    }
    
    @Test public void testLet2() {
        helpTCF("A.java","public class A { void m() { //@ assert 0 == (\\let int i = 0, int j = 2; i - j); \n}}"
                );
    }
    
    @Test public void testLet3() {
        helpTCF("A.java","public class A { void m() { //@ assert (\\let int i = 0; i); \n}}"
                ,"/A.java:1: incompatible types: int cannot be converted to boolean",41);
    }
    
    @Test public void testLet4() {
        helpTCF("A.java","public class A { void m() { //@ assert (\\let int i; i==0); \n}}"
                ,"/A.java:1: = expected",51);
    }
    
    @Test public void testLet5() {
        helpTCF("A.java","public class A { void m() { boolean i; //@ assert (\\let int i=0; i==0); \n i = true; }}"
                ,"/A.java:1: variable i is already defined in method m()",61
                );
    }
    
    @Test public void testLet6() {
        helpTCF("A.java","public class A { void m(boolean i) {  //@ assert (\\let int i=0; i==0); \n i = true; }}"
                ,"/A.java:1: variable i is already defined in method m(boolean)",60
                );
    }
    
    @Test public void testLet7() {
        helpTCF("A.java","public class A { boolean i; //@ invariant (\\let int i=0; i==0); \n  }"
                );
    }

    @Test public void testLet8() {
        helpTCF("A.java","public class A { void m(int j) {  //@ assert (\\let int i=0; i==j); \n  }}"
                );
    }
    
    @Test public void testLet9() {
        helpTCF("A.java","public class A { int j; //@ invariant (\\let int i=0; i==j); \n  }"
                );
    }

    @Test public void testLet10() {
        helpTCF("A.java","public class A { void m(boolean j) {  //@ assert (\\let int i=0; i==j); \n  }}"
                ,"/A.java:1: incomparable types: int and boolean",66);
    }
    
    @Test public void testLet11() {
        helpTCF("A.java","public class A { boolean j; //@ invariant (\\let int i=0; i==j); \n  }"
                ,"/A.java:1: incomparable types: int and boolean",59);
    }


    @Ignore  // FIXME - what is \same?
    @Test public void testSame() {
        helpTCF("A.java","public class A { //@ requires  i; also requires \\same; \n boolean m(boolean i) { return false; }\n}"
                );
    }
    @Ignore  // FIXME - what is \same?
    @Test public void testSame1() {
        helpTCF("A.java","public class A { //@ requires 1+\\same; \n boolean m(double i) { return false; }\n}",
                "/A.java:1: bad operand types for binary operator '+'\n  first type:  int\n  second type: boolean",32);
    }
    @Ignore // FIXME - should not allow \same inside expressions
    @Test public void testSame2() { 
        helpTCF("A.java","public class A { //@ requires i; also requires !\\same; \n boolean m(boolean i) { return false; }\n}"
                );
    }
    
    @Ignore // FIXME - should not allow \same without previous preconditions
    @Test public void testSame3() {
        helpTCF("A.java","public class A { //@ requires \\same; \n boolean m(double i) { return false; }\n}"
                );
    }
    
    @Ignore // FIXME - semantics of \same
    @Test public void testSame4() {
        helpTCF("A.java","public class A { //@ ensures \\same; \n boolean m(double i) { return false; }\n}"
                ,"/A.java:1: A \\same token may only be used in requires clauses",30
                );
    }

    // FIXME
//    @Test public void testLockCompare() {
//        expectedExit = 0;
//        helpTCF("A.java","public class A { Object o,oo; //@ invariant o < oo; \n }"
//                ,"/A.java:1: warning: Operators < and <= are deprecated as lock comparisons - use <# and <#= instead",47
//                );
//    }
    
    @Test public void testLockCompareX() {
        helpTCF("A.java","public class A { Integer o,oo; //@ invariant o < oo; \n }"
                );
    }
    
    // FIXME
//    @Test public void testLockCompare1() {
//        expectedExit = 0;
//        helpTCF("A.java","public class A { Object o,oo; //@ invariant o <= oo; \n }"
//                ,"/A.java:1: warning: Operators < and <= are deprecated as lock comparisons - use <# and <#= instead",47
//                );
//    }
    
    @Test public void testLockCompare1X() {
        helpTCF("A.java","public class A { Integer o,oo; //@ invariant o <= oo; \n }"
                );
    }
    
    @Test public void testLockCompare2() {
        helpTCF("A.java","public class A { Object o,oo; int i; //@ invariant o < true; \n }"
                ,"/A.java:1: bad operand types for binary operator '<'\n  first type:  java.lang.Object\n  second type: boolean",54
                );
    }
    
    @Test public void testLockCompare2X() {
        helpTCF("A.java","public class A { Integer o,oo; int i; //@ invariant o < 5; \n }"
                );
    }
    
    @Test public void testLockCompare2Y() {
        helpTCF("A.java","public class A { Object o,oo; int i; //@ invariant o < 5; \n }"
                ,"/A.java:1: bad operand types for binary operator '<'\n  first type:  java.lang.Object\n  second type: int",54
                );
    }
    
    @Test public void testLockCompare3() {
        helpTCF("A.java","public class A { Object o,oo; boolean b = o <= oo;  \n }"
                ,"/A.java:1: bad operand types for binary operator '<='\n  first type:  java.lang.Object\n  second type: java.lang.Object",45
                );
    }
    
    @Test public void testLockCompare4() {
        helpTCF("A.java","public class A { Object o,oo; boolean b = o <= oo;  \n }"
                ,"/A.java:1: bad operand types for binary operator '<='\n  first type:  java.lang.Object\n  second type: java.lang.Object",45
                );
    }
    
    @Test public void testLockCompareA() {
        helpTCF("A.java","public class A { Object o,oo; //@ invariant o <# oo; \n }"
                );
    }
    
    @Test public void testLockCompare1A() {
        helpTCF("A.java","public class A { Object o,oo; //@ invariant o <#= oo; \n }"
                );
    }
    
    @Test public void testFreshBad() {
        helpTCF("A.java","public class A { Object o,oo; //@ invariant \\fresh(o);  \n }"
                ,"/A.java:1: A \\fresh expression may not be in a invariant clause",52
                );
    }
    
    @Test public void testFreshWeirdError() {
        helpTCF("WeirdError.java",
                "public class WeirdError {\n" +
                " public Foo getFoo() { return null; }\n" +
                "}\n"
                ,"/WeirdError.java:2: cannot find symbol\n  symbol:   class Foo\n  location: class WeirdError",9
               // ,"/WeirdError.java:2: A \\result expression may not be used in the specification of a method that returns void",14
                );
    }
    
    @Test public void testFresh() {
        helpTCF("A.java","public class A { Object o,oo; //@ ensures \\fresh(o); \n void m() {} \n }"
                );
    }
    
    @Test public void testFresh2() {
        helpTCF("A.java","public class A { Object o,oo; //@ ensures \\fresh(o,oo); \n void m() {}  \n }"
                );
    }
    
    @Test public void testFresh3() {
        helpTCF("A.java","public class A { Object o,oo; //@ ensures \\fresh(); \n void m() {}  \n }"
                ,"/A.java:1: A \\fresh expression expects just 1 or 2 arguments, not 0",49
                );
    }
    
    @Test public void testFresh4() {
        helpTCF("A.java","public class A { int i; Object o,oo; //@ ensures   \\fresh(i); \n void m() {}  \n }"
                ,"/A.java:1: The argument of \\fresh must be of reference type",59
                );
    }
    
    @Test public void testFresh5() {
        helpTCF("A.java","public class A { int i; Object o,oo; //@ ensures   \\fresh(o) + 1 == 0; \n void m() {}  \n }"
                ,"/A.java:1: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: int",62
                );
    }
    
    @Test public void testFresh5Bad() {
        helpTCF("A.java","public class A { int i; Object o,oo; //@ ghost boolean k = \\fresh(o);  \n }"
                ,"/A.java:1: A \\fresh expression may not be in a jml declaration clause",67
        );
    }
    
    @Test public void testOnlyAssigned() {
        helpTCF("A.java","public class A { Object o,oo; //@ invariant \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o);  \n }"
                ,"/A.java:1: A \\only_assigned expression may not be in a invariant clause",59
                ,"/A.java:1: A \\only_accessed expression may not be in a invariant clause",80
                ,"/A.java:1: A \\only_captured expression may not be in a invariant clause",101
                ,"/A.java:1: A \\not_assigned expression may not be in a invariant clause",121
                ,"/A.java:1: A \\not_modified expression may not be in a invariant clause",141
                );
    }
    
    @Test public void testOnlyAssigned1() {
        helpTCF("A.java","public class A { Object o,oo; //@ ensures \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o); \n void m() {} \n }"
                );
    }
    
    @Test public void testOnlyAssigned2() {
        helpTCF("A.java","public class A { int i; Object o,oo; //@ ghost boolean k = \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o);  \n }"
                ,"/A.java:1: A \\only_assigned expression may not be in a jml declaration clause",74
                ,"/A.java:1: A \\only_accessed expression may not be in a jml declaration clause",95
                ,"/A.java:1: A \\only_captured expression may not be in a jml declaration clause",116
                ,"/A.java:1: A \\not_assigned expression may not be in a jml declaration clause",136
                ,"/A.java:1: A \\not_modified expression may not be in a jml declaration clause",156
        );
    }
    
    @Test public void testInformalComment() {
        helpTCF("A.java","public class A {\n //@ invariant (* stuff *);\n //@ ghost int k = (* stuff *);  \n }"
                ,"/A.java:3: incompatible types: boolean cannot be converted to int",20
        );
    }

    @Test public void testId() {
        helpTCF("A.java","public class A {\n //@ public model int duration;  \n void m() { //@ set duration = 0;\n } \n }"
//                ,"/A.java:2: Expected an identifier, found a JML keyword instead: duration",23
        );
    }

    // The following are situations that are not yet handled properly.
    // That is because model imports are treated just like normal imports,
    // so they can lead to incorrect name resolution in the Java code.

    // No errors but should have one: the use of List in the declaration of n should fail.
    @Test public void testModelImport1() {
        helpTCF("A.java","//@ model import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
        );
    }
    
    // This should fail for the ghost declaration but not for the Java declaration
    @Test public void testModelImport2() {
        helpTCF("A.java","import java.awt.*; //@ model import java.util.*;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:3: reference to List is ambiguous\n  both interface java.util.List in java.util and class java.awt.List in java.awt match",12
                ,"/A.java:4: reference to List is ambiguous\n  both interface java.util.List in java.util and class java.awt.List in java.awt match",2
        );
    }

    // This should fail for the Java declaration but not for the ghost declaration
    @Test public void testModelImport3() {
        helpTCF("A.java","import java.awt.*; import java.util.*;\n//@ model import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
        );
    }

    @Test public void testOKImport1() {
        helpTCF("A.java","import java.util.*;\n public class A {\n List n;  \n }"
        );
    }
    
    @Test public void testBadModelImport1() {
        helpTCF("A.java","//@ import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:1: An import statement in a JML comment must have a model modifier",5
        );
    }
    
    @Test public void testBadModelImport2() {
        helpTCF("A.java","/*@ model */ import java.util.List;\n public class A {\n  \n }"
                ,"/A.java:1: A model import declaration must be completely within a JML comment",14,13,13,34
        );
    }
    
    @Test public void testBadModelImport2a() {
        helpTCF("A.java","/*@ model */  public class A {\n  \n }"
                ,"/A.java:1: A Java declaration (not within a JML annotation) may not be either ghost or model",22
        );
    }
    
    @Test public void testBadModelImport3() { // FIXME - could be a better error message
        helpTCF("A.java","/*@ model import */ java.util.List;\n public class A {\n  \n }"
                ,"/A.java:1: Expected an identifier, found end of JML comment instead",18
                ,"/A.java:1: '.' expected",20
                ,"/A.java:1: package <error>.java.util does not exist",30
                ,"/A.java:1: package <error>.java.util does not exist",30
        );
    }
    
    // Bug: 3366092
    @Test public void testEnum1() {
        helpTCF("A.java","public class A {\n  enum E { X {} }; \n }"
        );
        
    }
    
    // Bug: 3366092
    @Test public void testEnum2() {
        helpTCF("A.java","public class A {\n  enum E { X {}; } \n }"
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3() {
        helpTCF("A.java","public class A {\n  public enum X { Y; X(){}; } \n }"
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3a() {
        helpTCF("A.java","public class A {\n  public enum X { Y; public X(){}; } \n }"
        ,"/A.java:2: modifier public not allowed here",29
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3b() {
        helpTCF("A.java","public class A {\n  public enum X { Y; protected X(){}; } \n }"
                ,"/A.java:2: modifier protected not allowed here",32
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3c() {
        helpTCF("A.java","public class A {\n  public enum X { Y; private X(){}; } \n }"
        );
        
    }
    
    // Bug: 3421143
    @Test public void testEnum4() {
        helpTCF("A.java","public class A {\n  public enum X { Y; public X m() { for (X c: values()) break; return Y; } } \n }"
        );
        
    }
    
    // Bug: 3373400
    @Test public void testBug4() {
        helpTCF("A.java","interface A<V> { /*@ instance ghost V r; @*/ \n }"
        );
        
    }
    
    // Bug: 3377329
    @Test public void testBug5() {
        helpTCF("A.java","public class A {\n"
                +"  public void test1(Object[] blub) {\n"
                +"    //@ loop_invariant 0<=i && i <= blub.length;\n"
                +"    for(int i=0; i< blub.length; i++) {\n"
                +"      /*@nullable @*/ Object b = blub[i];\n"
                +"      if (b == null)\n"
                +"        continue;\n"
                +"    }\n"
                +"  }\n"
                +"  public void test2(Object[] blub) {\n"
                +"    for(Object b : blub) {\n"
                +"      if (b == null)\n"
                +"        continue;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                );
    }
    
    // Bug: 3377329
    @Test public void testBug5a() {
        helpTCF("A.java","public class A {\n"
                +"  public void test1(Object[] blub) {\n"
                +"    //@ loop_invariant 0<=i && i <= blub.length;\n"
                +"    for(int i=0; i< blub.length; i++) {\n"
                +"      /*@nullable @*/ Object b = blub[i];\n"
                +"      if (b == null)\n"
                +"        break;\n"
                +"    }\n"
                +"  }\n"
                +"  public void test2(Object[] blub) {\n"
                +"    for(Object b : blub) {\n"
                +"      if (b == null)\n"
                +"        break;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                );
    }
    
    // Bug: 3388690
    @Test public void testBug6() {
    	expectedExit = 0;
        helpTCF("Test.java","public class Test {\n"
                +"private final int my_height; /*@ in height; @*/\n"
  
                +"  /*@ public model int height;\n"
                +"      in_redundantly height;\n"
                +"      public invariant 0 < height;\n"
                +"      public constraint \\old(height) == height;\n"
                +"      private represents height = my_height;\n"
                +"      private invariant 0 < my_height;\n"
                +"  @*/\n"
  
                +"  public Test() {\n"
                +"    my_height = 1;\n"
                +"  }\n"
                +"}\n"
                ,"/Test.java:4: warning: Do not include a datagroup in itself: height",22
                ,"/Test.java:4: warning: Do not include a datagroup in itself: height",22
        );
        
    }
    
    @Test public void testBug6a() {
        helpTCF("Test.java","public class Test {\n"
                +"private final int my_height; /*@ in height; @*/\n"
  
                +"  /*@ public model int height;\n"
                +"      in_redundantly height2;\n"
                +"  @*/\n"
  
                +"  /*@ public model int height2;\n"
                +"      in_redundantly height;\n"
                +"  @*/\n"
  
                +"  public Test() {\n"
                +"    my_height = 1;\n"
                +"  }\n"
                +"}\n"
                ,"/Test.java:2: This field participates in a circular datagroup inclusion chain: my_height -> height -> height2 -> height",19
                ,"/Test.java:3: This field participates in a circular datagroup inclusion chain: height -> height2 -> height",24
                ,"/Test.java:6: This field participates in a circular datagroup inclusion chain: height2 -> height -> height2",24
        );
        
    }
    
    @Test
    public void typeserr() {
        helpTCF("A.java",
           "class A { //@ ghost boolean b4 = \\type(java.util.Map<java.util.List<?>,?>) <: \\type(java.util.List<?>);\n}"
                ,"/A.java:1: Wildcards are not allowed within \\type expressions: java.util.Map<java.util.List<?>, ?>",69
                ,"/A.java:1: Wildcards are not allowed within \\type expressions: java.util.Map<java.util.List<?>, ?>",72
                ,"/A.java:1: Wildcards are not allowed within \\type expressions: java.util.List<?>",100
           );
    }
        

    
    @Test public void testSwitchWithStrings() {
        helpTCF("A.java"," class A { public void m(String s) { switch (s) { case \"David\": case \"Cok\": System.out.println(\"me\"); break; default: System.out.println(\"not me\"); } } }"
                );
    }

    @Test public void testQuantifiedExpression() {
        helpTCF("A.java"," class A { /*@ public invariant (\\sum Integer i; 0<=i && i < 6; new Object()); */ }"
        		,"/A.java:1: The value expression of a sum or product expression must be a numeric type, not java.lang.Object",65
                );
    }

    // FIXME - does not appear to be working yet
//    @Test public void testDiamondGenerics() {
//        helpTCF("A.java","public class A { java.util.List<Integer> list = new java.util.LinkedList<>(); } }"
//                );
//    }

    @Test public void testMultiCatch() {
        helpTCF("A.java","public class A { public void m(int i) { try { if (i == 0) throw new ArrayIndexOutOfBoundsException(); if (i == 1) throw new NullPointerException(); } catch ( final ArrayIndexOutOfBoundsException | NullPointerException e) {}  } }"
                );
    }


    @Test public void testTryWithResources() {
        helpTCF("A.java","import java.io.*; public class A { public void m(int i) { try ( FileReader r = new FileReader(\"\") ) {   } catch (final IOException e) {} finally {} } }"
                );
    }

    @Test public void testErrorGitBug609() {
    	addMockFile("$A/B.java","package p; public class B{}");
        helpTCF("A.java","package p; public class A implements Cloneable { private B b; A() { b = new B(); }}"
                ,"/A.java:1: cannot find symbol\n  symbol:   class B\n  location: class p.A",58
				,"/A.java:1: cannot find symbol\n  symbol:   class B\n  location: class p.A",77
        		);
    }

    @Test public void testJmlLabelExpression() {
        helpTCF("TestJava.java","package tt; \n"
                +"public class TestJava { \n"

                +"  public int m1bad(boolean b, int k) {\n"
                +"    int j = 0;\n"
                +"    //@ ghost boolean bb = (\\forall int i; 0<=i && i <=4; 0!=(\\lbl LBL i));\n"
                +"    return 1;\n"
                +"  }\n"
                

                +"}"
                ,"/TestJava.java:5: A JML label expression may not be within a quantified or set-comprehension expression",63
                );
    }

    @Test public void testKeywords() {
        helpTCF("TestJava.java","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ model public void m1bad(java.util.function.Function<Integer,Integer> f) ;\n"                

                +"}"
                );
    }

    @Test public void testSpecCaseVisibility() {
        expectedExit = 0; // Only warnings
        helpTCF("TestJava.java","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ public behavior requires true;\n"
                +"  public void m1p() {\n"
                +"  }\n"
                
                +"  //@ protected behavior requires true;\n"
                +"  public void m1r() {\n"
                +"  }\n"
                
                +"  //@ behavior requires true;\n"
                +"  public void m1k() {\n"
                +"  }\n"
                
                +"  //@ private behavior requires true;\n"
                +"  public void m1v() {\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  public void m1() {\n"
                +"  }\n"
                
                +"  //@ public behavior requires true;\n"  // Warning
                +"  protected void m2p() {\n"
                +"  }\n"
                
                +"  //@ protected behavior requires true;\n"
                +"  protected void m2r() {\n"
                +"  }\n"
                
                +"  //@ behavior requires true;\n"
                +"  protected void m2k() {\n"
                +"  }\n"
                
                +"  //@ private behavior requires true;\n"
                +"  protected void m2v() {\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  protected void m2() {\n"
                +"  }\n"
                
                +"  //@ public behavior requires true;\n" // Warning
                +"  private void m3p() {\n"
                +"  }\n"
                
                +"  //@ protected behavior requires true;\n" // Warning
                +"  private void m3r() {\n"
                +"  }\n"
                
                +"  //@ behavior requires true;\n"  // Warning
                +"  private void m3k() {\n"
                +"  }\n"
                
                +"  //@ private behavior requires true;\n"
                +"  private void m3v() {\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  private void m3() {\n"
                +"  }\n"
                
                +"  //@ public behavior requires true;\n" // Warning
                +"  void m4p() {\n"
                +"  }\n"
                
                +"  //@ protected behavior requires true;\n" // Warning
                +"  void m4r() {\n"
                +"  }\n"
                
                +"  //@ behavior requires true;\n"
                +"  void m4k() {\n"
                +"  }\n"
                
                +"  //@ private behavior requires true;\n"
                +"  void m4v() {\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  void m4() {\n"
                +"  }\n"
                

                +"}"
                ,"/TestJava.java:18: warning: There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:33: warning: There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:36: warning: There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:39: warning: There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:48: warning: There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:51: warning: There is no point to a specification case having more visibility than its method",7
                );
    }

    
}
