package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typeclauses extends TCBase {

    String eol = "\n";  // Just newline for Windows also
    
    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Tests typechecking an invariant clause - OK*/
    @Test
    public void testInvariant() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ invariant b;\n}");
    }

    /** Tests typechecking an invariant clause - bad type*/
    @Test
    public void testInvariant2() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ invariant k;\n}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",15);
    }

    /** Tests typechecking an invariant clause - OK from Boolean*/
    @Test
    public void testInvariant3() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ invariant bb;\n}");
    }

    /** Tests static lookup for invariant */
    @Test
    public void testInvariant4() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ static invariant bb;\n}"
                ,"/TEST.java:2: non-static variable bb cannot be referenced from a static context",22
                );
    }

    /** Tests static lookup for invariant */
    @Test
    public void testInvariant5() {
        helpTC(" class A { int k; boolean b; static Boolean bb; \n//@ static invariant bb;\n}");
    }

    /** Tests typechecking an constraint clause - OK*/
    @Test
    public void testConstraint() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ constraint b;\n}");
    }

    /** Tests typechecking an constraint clause - bad type*/
    @Test
    public void testConstraint2() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ constraint k;\n}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",16);
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint3() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ constraint bb;\n}");
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint4() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ constraint bb for \\everything;\n}");
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint5() {
        helpTC(" class A { public A(){} void m(int i) {} Boolean bb; \n//@ constraint bb for A(), m, m(int), m(Object);\n}"
                ,"/TEST.java:2: Constructors are not allowed as methods in non-static constraint clauses",23
                ,"/TEST.java:2: incompatible types: java.lang.Object cannot be converted to int",39
                );
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint5s() {
        helpTC(" class A { void m(int i) {} static Boolean bb; \n//@ static constraint bb for A();\n}"
                );
    }

    /** Tests static lookup for constraint */
    @Test
    public void testConstraint6() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ static constraint bb ;\n}"
                ,"/TEST.java:2: non-static variable bb cannot be referenced from a static context",23
                );
    }

    /** Tests static lookup for constraint */
    @Test
    public void testConstraint7() {
        helpTC(" class A { void m(int i) {} static Boolean bb; \n//@ static constraint bb ;\n}");
    }

    // TODO - the testConstraintM... tests are not implemented
    @Test
    public void testConstraintM() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for m;\n}");
    }

    @Test
    public void testConstraintM1() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for mm;\n}");
    }

    @Test
    public void testConstraintM2() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for this.m;\n}");
    }

    @Test
    public void testConstraintM3() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for A.m;\n}");
    }

    @Test
    public void testConstraintMA() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for m(int);\n}");
    }

    @Test
    public void testConstraintMA1() {
        helpTC(" class A { void m(int i) {} Boolean bb; \n//@ constraint bb for mm(int);\n}"
                ,"/TEST.java:2: cannot find symbol\n  symbol:   method mm(int)\n  location: class A",23
                );
    }

    @Test
    public void testConstraintMA2() {
        helpTC(" class A { void m(int i[],Object o) {} void m(int i) {} Boolean bb; \n//@ constraint bb for this.m(int[],Object);\n}");
    }

    @Test
    public void testConstraintMA3() {
        helpTC(" class A { void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for a.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA3s() {
        helpTC(" class A { static void m(Integer i) {} Boolean bb; \n//@ constraint bb for A.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA3e() {
        helpTC(" class A { void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for A.m(java.lang.Integer);\n}"
                ,"/TEST.java:2: non-static method m(java.lang.Integer) cannot be referenced from a static context",25
                );
    }

    @Test
    public void testConstraintMA3se() {
        helpTC(" class A { static void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for a.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA4() {
        helpTC(" class A extends B { Boolean bb; \n//@ constraint bb for m(java.lang.Integer);\n} class B { void m(Integer i) {} }"
                ,"/TEST.java:2: The method must be a direct member of the class containing the constraint clause",23
                );
    }

    @Test
    public void testConstraintMA5() {
        helpTC(" class A { Boolean bb; \n//@ constraint bb for B.m(java.lang.Integer);\n} class B { void m(Integer i) {} }"
                ,"/TEST.java:2: non-static method m(java.lang.Integer) cannot be referenced from a static context",25  // FIXME - not sure this error is correct
                ,"/TEST.java:2: The method must be a direct member of the class containing the constraint clause",23
                );
    }

    /** Tests typechecking an axiom clause - OK*/
    @Test
    public void testAxiom() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ axiom b;\n}");
    }

    /** Tests typechecking an axiom clause - bad type*/
    @Test
    public void testAxiom2() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ axiom k;\n}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",11);
    }

    /** Tests typechecking an axiom clause - OK from Boolean*/
    @Test
    public void testAxiom3() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ axiom bb;\n}");
    }

    /** Tests typechecking an initially clause - OK*/
    @Test
    public void testInitially() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ initially b;\n}");
    }

    /** Tests typechecking an initially clause - bad type*/
    @Test
    public void testInitially2() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ initially k;\n}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",15);
    }

    /** Tests typechecking an initially clause - OK from Boolean*/
    @Test
    public void testInitially3() {
        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ initially bb;\n}");
    }

    /** Tests typechecking an initially clause - OK from Boolean*/
    @Test
    public void testInitially4() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ initially x;\n}",
                "/A.java:2: cannot find symbol\n  symbol:   variable x\n  location: class A",15);
    }

    /** Tests initially may be static */
    @Test
    public void testInitially5() {
        helpTCF("A.java"," class A { int k; boolean b; Boolean bb; \n//@ static initially b;\n}"
                ,"/A.java:2: non-static variable b cannot be referenced from a static context",22
                );
    }

    @Test
    public void testRepresents() {
        helpTCF("A.java","public class A {\n //@ model int i; represents i = true;\n}"
                ,"/A.java:2: incompatible types: boolean cannot be converted to int",34
                );
    }

    @Test
    public void testRepresents1() {
        helpTCF("A.java","public class A {\n //@ model int i; represents i <- true;\n}"
                ,"/A.java:2: incompatible types: boolean cannot be converted to int",35
                );
    }

    @Test
    public void testRepresents2() {
        helpTCF("A.java","public class A {\n //@ model int i; represents i \\such_that 0;\n}"
                ,"/A.java:2: incompatible types: int cannot be converted to boolean",43
                );
    }

    @Test
    public void testRepresents3() {
        helpTCF("A.java","public class A {\n //@ model int i; represents j = 0;\n}"
                ,"/A.java:2: cannot find symbol\n  symbol:   variable j\n  location: class A",30
                );
    }
    
    @Test
    public void testRepresents4() {
        helpTCF("A.java","public class A {\n //@ model int i; represents i :0;\n}"
                ,"/A.java:2: A represents clause must have a = or \\such_that after the identifier",32
                );
    }
    
    @Test
    public void testRepresents5() {
        helpTCF("A.java","public class A {\n //@ model int j; represents j = ;\n}"
                ,"/A.java:2: illegal start of expression",34
                );
    }
    
    @Test
    public void testRepresents6() {
        helpTCF("A.java","public class A {\n //@ model int i; represents j = 0\n}"
                ,"/A.java:2: The expression is invalid or not terminated by a semicolon",35
                ,"/A.java:2: cannot find symbol"+eol+"  symbol:   variable j"+eol+"  location: class A",30
                );
    }
    
    @Test
    public void testRepresents7() {
        helpTCF("A.java","public class A {\n //@ model int i; represents x = 0\n}"
                ,"/A.java:2: The expression is invalid or not terminated by a semicolon",35
                ,"/A.java:2: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",30
                );
    }
    
    @Test
    public void testRepresents8() {
        helpTCF("A.java","public class A {\n //@ model int i; represents x.* = 0\n}"
                ,"/A.java:2: Expected an identifier after the dot in this context",32
                ,"/A.java:2: A represents clause must have a = or \\such_that after the identifier",37
                ,"/A.java:2: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",30
                );
    }
    
    @Test  // FIXME - why is strict on here? isn't the default false
    public void testRepresents9() {
        helpTCF("A.java","public class A {\n //@ model int i; represents x[*] = 0\n}"
                ,"/A.java:2: Strict JML does not allow the [*] syntax",32
                ,"/A.java:2: The expression is invalid or not terminated by a semicolon",38
                ,"/A.java:2: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",30
                );
    }
    
    @Test
    public void testRepresents10() {
        helpTCF("A.java","public class A {\n //@ model int i; represents x[3] = 0;\n}"
                ,"/A.java:2: cannot find symbol\n  symbol:   variable x\n  location: class A",30
                );
    }
    
    @Test
    public void testRepresents11() {
        helpTCF("A.java","public class A {\n //@ model int i; static represents i = 0;\n}"
                ,"/A.java:2: A represents clause and its associated model field must both be static or both not be static",26
                );
    }
    
    @Test
    public void testRepresents12() {
        helpTCF("A.java","public class A {\n //@ model static int i; represents i = 0;\n}"
                ,"/A.java:2: A represents clause and its associated model field must both be static or both not be static",26
                );
    }
    
    @Test
    public void testRepresents13() {
        helpTCF("A.java","public class A {\n //@ ghost int i; represents i = 0;\n}"
                ,"/A.java:2: The target of a represents clause must be a model field",19
                );
    }
    
    @Test
    public void testRepresents14() {
        helpTCF("A.java","public class A {\n int i; //@ represents i = 0;\n}"
                ,"/A.java:2: The target of a represents clause must be a model field",13
                );
    }
    
    @Test
    public void testRepresents13a() {
        addMockFile("$A/A.jml","public class A {\n //@ ghost int i; represents i = 0;\n}");
        helpTCF("A.java","public class A {\n }"
                ,"/$A/A.jml:2: The target of a represents clause must be a model field",19
                );
    }
    
    @Test
    public void testRepresents14a() {
        addMockFile("$A/A.jml","public class A {\n //@ represents i = 0;\n}");
        helpTCF("A.java","public class A {\n int i; \n}"
                ,"/$A/A.jml:2: The target of a represents clause must be a model field",6
                );
    }

    /** Check that the target of a static represents clause is in the same class */
    @Test
    public void testRepresents15() {
        helpTCF("A.java","public class A extends B {\n //@ static represents i = 0;\n} class B { //@ static model int i; \n}"
                ,"/A.java:2: A represents clause must be declared in the same class as the static model field it represents",13
                );
    }
    
    /** Check that the rhs of a static represents clause contains only static fields */
    @Test
    public void testRepresents16() {
        helpTCF("A.java","public class A {\n static int k; int j; //@ model static int i; static represents i = k;\n}"
                );
    }
    
    /** Check that the rhs of a static represents clause contains only static fields */
    @Test
    public void testRepresents16a() {
        helpTCF("A.java","public class A {\n static int k; int j; //@ model static int i; static represents i = j;\n}"
                ,"/A.java:2: non-static variable j cannot be referenced from a static context",69
                );
    }
    
    /** Check that warning that <- is deprecated */
    @Test
    public void testRepresents17() {
        expectedExit = 0;
        main.addOptions("-deprecation");
        helpTCF("A.java","public class A {\n static int j; //@  model static int i; static represents i <- j;\n}"
                ,"/A.java:2: warning: The left arrow is deprecated in represents clauses, use = instead",61
                );
    }
    

    @Test
    public void testMisc() {
        helpTCF("A.java","public class A {\n //@ ensures ((boolean)\\result);\n int m() { return 0; }}"
                ,"/A.java:2: incompatible types: int cannot be converted to boolean",24
        );
    }
    
    @Test
    public void testMisc2() {
        helpTCF("A.java","public class A {\n //@ ensures ((short)\\result) == 0;\n int m() { return 0; }}"
        );
    }
    
    @Test
    public void testMisc3() {
        helpTCF("A.java","public class A {\n //@ public normal_behavior ensures true; public model boolean m(); \n }"
        );
    }
    
    @Test
    public void testForall() {
        helpTCF("A.java","public class A {\n //@ forall int i,j; old boolean k=true, m = false; requires i == 0; \n public void m() {}}"
                );
    }
    
    @Test
    public void testForall2() {
        helpTCF("A.java","public class A {\n //@ forall int i=0,j; old boolean k, m = false; requires i == 0; \n public void m() {}}"
                ,"/A.java:2: A forall method clause declaration must not have initializers",19
                ,"/A.java:2: A old method clause variable must have an initializer",36
        );
    }
    
    @Test
    public void testForall3() {
        helpTCF("A.java","public class A {\n //@ old int i=true; old boolean m=0; requires i == 0; \n public void m() {}}"
                ,"/A.java:2: incompatible types: boolean cannot be converted to int",16
                ,"/A.java:2: incompatible types: int cannot be converted to boolean",36
                );
    }
    
    @Test
    public void testForall4() {
        helpTCF("A.java","public class A {\n //@ forall int j; old int k=0; requires i+j<k; \n public void m(int i) {}}"
                );        // OK
    }
    
    @Test
    public void testForall5() {
        helpTCF("A.java","public class A {\n //@ forall boolean j; old boolean  k=true; requires i+j<k; \n public void m(boolean i) {}}"
                ,"/A.java:2: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: boolean",55
                );        
    }
    
    @Test
    public void testForall6() {
        helpTCF("A.java","public class A { int i,j,k; \n //@ forall boolean j; old boolean k=true; requires i+j<k; \n public void m(boolean i) {}}"
                ,"/A.java:2: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: boolean",54
                );        
    }
    
    @Test
    public void testForall7() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCF("A.java","public class A { \n //@ forall int i; old int k=0   ; requires i<k; \n public void m(int i) {}}"
                ,"/A.java:2: variable i is already defined in method m(int)",17
                );        
    }
    
    @Test
    public void testForall8() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCF("A.java","public class A { \n //@ forall int k; old int k=0   ; requires i<k; \n public void m(int i) {}}"
                ,"/A.java:2: variable k is already defined in method m(int)",28
                );        
    }
    
    @Test
    public void testForall9() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCF("A.java","public class A { \n //@ forall int j; old int k=0   ; requires i<k; \n//@{| forall int m; ensures k<m; also ensures k<m; |} \n public void m(int i) {}}"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable m\n  location: class A",49
                );        
    }
    
    @Test
    public void testForall10() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCF("A.java","public class A { \n //@ forall int j; old int k=0   ; requires i<k; \n//@{| forall int k; ensures k<m; also ensures i==0; |} \n public void m(int i) {}}"
                ,"/A.java:3: variable k is already defined in method m(int)",18
                ,"/A.java:3: cannot find symbol\n  symbol:   variable m\n  location: class A",31
                );        
    }

    @Test
    public void testSignals() { //OK
        helpTCF("A.java","public class A {\n//@signals(Exception e) true; \n void m(){}}");
    }

    @Test
    public void testSignals1() {//OK
        helpTCF("A.java","public class A {\n//@signals(Exception) true; \n void m(){}}");
    }

    @Test
    public void testSignals2() { //Bad type
        helpTCF("A.java","public class A {\n//@signals(Object e) true; \n void m(){}}",
                "/A.java:2: incompatible types: java.lang.Object cannot be converted to java.lang.Exception",12);
    }

    @Test
    public void testSignals3() { //Bad syntax
        helpTCF("A.java","public class A {\n//@signals true; \n void m(){}}",
                "/A.java:2: Expected a left parenthesis after a signals keyword",12);
    }

    @Test
    public void testSignals4() { //OK
        helpTCF("A.java","public class A {\n//@signals(RuntimeException ) ; \n void m(){}}"
                );
    }

    @Test
    public void testSignals5() { //Bad type
        helpTCF("A.java","public class A {\n//@signals(java.io.IOException e) 2; \n void m(){}}",
                "/A.java:2: incompatible types: int cannot be converted to boolean",35);
    }

    @Test
    public void testSignals6() { //Bad type
        helpTCF("A.java","public class A {\n//@signals(int e) true; \n void m(){}}",
                "/A.java:2: incompatible types: int cannot be converted to java.lang.Exception",12);
    }

    @Test
    public void testSignals7() { //OK - scoping
        helpTCF("A.java","public class A {\n//@signals(java.io.IOException e) e==null; \n void m(){}}");
    }

    @Test
    public void testSignalsOnly() { //OK
        helpTCF("A.java","public class A {\n//@signals_only \\nothing;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly1() { //OK
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly2() { //OK
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException,Exception;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly3() {
        helpTCF("A.java","public class A {\n//@signals_only ;\nvoid m() {}}",
                "/A.java:2: Use \\nothing to denote an empty list of exceptions in a signals_only clause",17);
    }

    @Test
    public void testSignalsOnly4() {
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException java.lang.Exception;\nvoid m() {}}",
                "/A.java:2: Missing comma or otherwise ill-formed type name",34);
    }

    @Test
    public void testSignalsOnly5() {
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException,;\nvoid m() {}}",
                "/A.java:2: illegal start of type",34);
    }

    @Test
    public void testSignalsOnly6() {
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException,,RuntimeException;\nvoid m() {}}",
                "/A.java:2: illegal start of type",34);
    }

    @Test
    public void testSignalsOnly7() {
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException\nvoid m() {}}",
                "/A.java:2: Invalid expression or missing semicolon here",33);
    }

    @Test
    public void testSignalsOnly8() {
        helpTCF("A.java","public class A {\n//@signals_only RuntimeException[];\nvoid m() {}}",
                "/A.java:2: incompatible types: java.lang.RuntimeException[] cannot be converted to java.lang.Throwable",33);
    }

    @Test
    public void testSignalsOnly9() {
        helpTCF("A.java","public class A {\n//@signals_only int;\nvoid m() {}}",
                "/A.java:2: incompatible types: int cannot be converted to java.lang.Throwable",17);
    }

    @Test
    public void testSignalsOnly10() {
        helpTCF("A.java","public class A {\n//@signals_only Q;\nvoid m() {}}",
                "/A.java:2: cannot find symbol\n  symbol:   class Q\n  location: class A",17);
    }
    
    @Test
    public void testIn() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n int n; //@ in k; \n}"
                );
    }
    
    @Test
    public void testIn2() {
        helpTCF("A.java","public class A extends B{\n protected int k; \n int n; //@ in k, this.k, super.kk; \n} class B { //@ model int kk; \n}"
                ,"/A.java:3: Datagroups in \"in\" and \"maps\" clauses must be model variables",16
                ,"/A.java:3: Datagroups in \"in\" and \"maps\" clauses must be model variables",19
                );
    }
    
    @Test
    public void testIn2a() {
        helpTCF("A.java","public class A extends B{\n /*@ spec_public */ protected int k; \n int n; //@ in k, this.k, super.kk; \n} class B { //@ model int kk; \n}"
                );
    }
    
    @Test
    public void testIn3() {
        helpTCF("A.java","public class A {\n /*@ spec_public */ protected int k; \n int n; //@ in m; \n}"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable m\n  location: class A",16
                );
    }
    
    @Test
    public void testIn4() {
        helpTCF("A.java","public class A {\n //@ model static int m; \n int n; //@ in m; \n}"
                ,"/A.java:3: A non-static variable may not be in a static datagroup",16
                );
    }
    
    @Test
    public void testMaps() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n A next; //@ maps next.next \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps2() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n A[] next; //@ maps next[*].next \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps2b() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n A[] next; //@ maps next[*] \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps3() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n A[] next; //@ maps next[2 .. 3].next \\into k,k; \n}"
        );
    }
    
    @Test
    public void testMaps4() {
        helpTCF("A.java","public class A {\n //@ model JMLDataGroup k; \n A[] next; //@ maps next[2].next \\into this.k; \n}"
        );
    }
    
    // TODO - should have some tests checking recovery in maps clauses
    
    @Test
    public void testInitializer() {
        helpTCF("A.java","public class A {\n //@initializer static_initializer \n}"
        );
    }

    @Test
    public void testInitializer1() {
        helpTCF("A.java","public class A {\n //@initializer static_initializer initializer static_initializer\n}"
                ,"/A.java:2: Only one initializer specification and one static_initializer specification are allowed",36
                ,"/A.java:2: Only one initializer specification and one static_initializer specification are allowed",48
        );
    }

    /** Tests that specs get associated with the initializer */
    @Test
    public void testInitializer2() {
        helpTCF("A.java","public class A {\n public int i; public static int j; //@ ensures i==0; initializer ensures j == 0; static_initializer \n}"
        );
    }

    /** Tests that variable references in a static initializer must be static */
    @Test
    public void testInitializer3() {
        helpTCF("A.java","public class A {\n public int i; public static int j; //@ ensures i == 0; static_initializer \n}"
                ,"/A.java:2: non-static variable i cannot be referenced from a static context",49
        );
    }

    @Test
    public void testInitializer4() {
        addMockFile("$A/A.jml","public class A {\n public int i; public static int j; //@ ensures i == 0; static_initializer \n}");
        helpTCF("A.java","public class A {\n public int i; public static int j;  \n}"
                ,"/$A/A.jml:2: non-static variable i cannot be referenced from a static context",49
        );
    }

    @Test
    public void testInitializer5() {
        addMockFile("$A/A.jml","public class A {\n int i; static int j; static {} \n}");
        helpTCF("A.java","public class A {\n int i; static int j;  \n}"
                ,"/$A/A.jml:2: Initializer blocks are not allowed in specifications",30
        );
    }

    @Test
    public void testInitializer6() {
        helpTCF("A.java","public class A {\n {} static {} \n}"
        );
    }

    @Test
    public void testInitializer7() {
        helpTCF("A.java","public class A {\n //@ {} static {} {} static {}\n}"
        );
    }

    /** Tests that specs are parsed with the Java initializer */
    @Test
    public void testInitializer8() {
        helpTCF("A.java","public class A {\n public int i; static public int j; //@ ensures i==0; \n {} //@ ensures i==0; \n static {} \n}"
                ,"/A.java:3: non-static variable i cannot be referenced from a static context",17
        );
    }

    @Test
    public void testInitializer9() {
        helpTCF("A.java","public class A {int i; static int j; \n \n static { i = 0; } \n}"
                ,"/A.java:3: non-static variable i cannot be referenced from a static context",11
        );
    }

    @Test
    public void testInitializer10() {
        helpTCF("A.java","public class A {public int i; public static int j; \n //@ ensures i==0; \n static { i = 0; } \n}"
                ,"/A.java:3: non-static variable i cannot be referenced from a static context",11
                ,"/A.java:2: non-static variable i cannot be referenced from a static context",14
        );
    }

    // OK
    @Test
    public void testMonitorsFor() {
        helpTCF("A.java","public class A {A a; Object i,j,k; //@ monitors_for i = j,a.k,Object.class; \n }"
        );
    }
    
    @Test
    public void testMonitorsFor1() {
        helpTCF("A.java","public class A {Object i,j,k; int m; //@ monitors_for i = 5; \n }"
                ,"/A.java:1: The expression in a monitors_for clause must have reference type",59
        );
    }
    
    @Test
    public void testMonitorsFor2() {
        helpTCF("A.java","public class A {Object i,j,k; int m; //@ monitors_for i <- m; \n }"
                ,"/A.java:1: The expression in a monitors_for clause must have reference type",60
        );
    }
    
    // OK - static does not matter
    @Test
    public void testMonitorsFor3() {
        helpTCF("A.java","public class A {Object i,j; static Object k;  //@ monitors_for k = i,A.k; \n }"
        );
    }
    
    @Test
    public void testMonitorsFor4() {
        helpTCF("A.java","public class A {Object i,j; static Object k;  //@ monitors_for k = Object; \n }"
                ,"/A.java:1: cannot find symbol\n  symbol:   variable Object\n  location: class A",68
        );
    }
    
    @Test
    public void testMonitorsFor5() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ monitors_for z = i; \n } class B { public Object z; }"
                ,"/A.java:1: The identifier must be a member of the enclosing class: z is in B instead of A",74
        );
    }
    
    //OK
    @Test
    public void testReadable() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable j if i == null; writable j if i == null; \n } class B { public Object z; }"
        );
    }
    
    @Test
    public void testReadable1() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if i == null; writable k if i == null; \n } class B { public Object z; }"
                ,"/A.java:1: non-static variable i cannot be referenced from a static context",75
                ,"/A.java:1: non-static variable i cannot be referenced from a static context",100
        );
    }
    
    @Test
    public void testReadable2() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable z if i == null; writable z if i == null; \n } class B { Object z; }"
                ,"/A.java:1: The identifier must be a member of the enclosing class: z is in B instead of A",70
                ,"/A.java:1: The identifier must be a member of the enclosing class: z is in B instead of A",95
        );
    }

    //OK
    @Test
    public void testReadable3() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if k == null; writable k if k == null; \n } class B { public Object z; }"
        );
    }
    
    //OK
    @Test
    public void testReadable4() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable i if this == null; writable i if this == null; \n } class B { public Object z; }"
        );
    }
    
    @Test
    public void testReadable5() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if this == null; writable k if this == null; \n } class B { public Object z; }"
                ,"/A.java:1: non-static variable this cannot be referenced from a static context",75
                ,"/A.java:1: non-static variable this cannot be referenced from a static context",103
        );
    }
    
    //OK
    @Test
    public void testReadable6() {
        helpTCF("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if Object.class == null; writable k if Object.class == null; \n } class B { public Object z; }"
        );
    }
    
}

