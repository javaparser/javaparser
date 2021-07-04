package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class QueryPure extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    @Test
    public void testClass1() {
        helpTCF("A.java",
                "//@ pure\n" +  // OK
                "public class A { } \n"
        );
    }
    
    @Test
    public void testClass2() {
        helpTCF("A.java",
                "//@ query\n" +   // OK
                "public class A { } \n"
        );
    }

    @Test
    public void testClass3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Query\n" +  // OK
                "public class A { } \n"
        );
    }

    @Test
    public void testClass4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Pure\n" +  // OK
                "public class A { } \n"
        );
    }

    @Test
    public void testClass5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Pure @Query\n" +   // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",7
        );
    }

    @Test
    public void testClass6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "//@ pure query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",10
        );
    }

    @Test
    public void testClass7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Pure //@ query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",11
        );
    }

    @Test
    public void testClass8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Pure //@ pure\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: org.jmlspecs.annotation.Pure is not a repeatable annotation type",11 // Changed location in Java8
        );
    }

    @Test
    public void testClass9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "@Query //@ query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: org.jmlspecs.annotation.Query is not a repeatable annotation type",12 // CHanged location in Java8
        );
    }

    @Test
    public void testMethod1() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Query\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    @Test
    public void testMethod2() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ query\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    @Test
    public void testMethod3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    @Test
    public void testMethod4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@pure\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    @Test
    public void testMethod5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ pure query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",12
        );
    }

    @Test
    public void testMethod6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Query @Pure\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",3
        );
    }

    @Test
    public void testMethod7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure //@ query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",13
        );
    }

    @Test
    public void testMethod8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Query //@ query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: org.jmlspecs.annotation.Query is not a repeatable annotation type",14
        );
    }

    @Test
    public void testMethod9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure //@ pure\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: org.jmlspecs.annotation.Pure is not a repeatable annotation type",13
        );
    }

    @Test
    public void testCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ secret public model JMLDataGroup value;\n" +
                "  @Secret protected Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query(\"value\") public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }
        
    @Test
    public void testSimplerCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ model public secret Object value;\n" +
                "  @Secret protected Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }

    @Test
    public void testAnotherCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; \n" + // Requires allowing non-model fields to be datagroups
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query(\"cache\") public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }

    @Test
    public void testAnotherValidExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + // To use the implicit declaration, value here must be after the Query
                "} \n"
        );
    }

    @Test
    public void testInvariant() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + // To use the implicit declaration, value here must be after the Query
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute();\n" +
                "} \n"
        );
    }

    @Test
    public void testForwardRef() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ secret model Object value;\n" + // we're allowing forward reference
                "} \n"
        );
    }

    @Test
    public void testCircular() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ secret model Integer cache ; //@ in value; \n" + 
                "  //@ secret model Object value; in cache; \n" + // error - circular
                "} \n"
                ,"/A.java:3: This field participates in a circular datagroup inclusion chain: cache -> value -> cache",28
                ,"/A.java:4: This field participates in a circular datagroup inclusion chain: value -> cache -> value",27
        );
    }

    @Test
    public void testCircularSelf() {
        expectedExit = 0;
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ secret model Object value; in value; \n" + // warning - circular
                "} \n"
                ,"/A.java:3: warning: Do not include a datagroup in itself: value",37
        );
    }

    @Test
    public void testQuery0() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; //@ in value; \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }

    @Test
    public void testQuery1() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ model secret public Object value;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == cache;\n" +  // ERROR - no use of secret in specs
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
                ,"/A.java:6: Secret fields may not be read in non-secret context: cache",26
        );
    }

    @Test
    public void testQuery2() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ model secret Object value;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return cache; }\n" + // ERROR - no use of secret in open method
                "} \n"
                ,"/A.java:8: Secret fields may not be read in non-secret context: cache",29
        );
    }

    @Test
    public void testQuery3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { f = 0; if (cache == null) cache = compute(); return cache; }\n" + // ERROR - no assignment except to secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:5: The field f is not writable since it is not in the value secret datagroup",31
        );
    }

    @Test
    public void testQuery4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { q = 0; if (cache == null) cache = compute(); return cache; }\n" + // ERROR - no assignment except to own secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:7: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",31
                ,"/A.java:7: The field q is not writable since it is not in the value secret datagroup",31
        );
    }

    @Test
    public void testQuery5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute() + q; return cache; }\n" + // ERROR - no reading other secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:7: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",70
        );
    }

    @Test
    public void testQuery6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute() + q; return cache; }\n" + // OK - q is nested in value
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
        );
    }

    @Test
    public void testQuery7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret public int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" + 
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" +// ERROR - no reading other secret
                "} \n"
                ,"/A.java:11: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",80
        );
    }

    // Note the difference between this test and the one below - here the attempt to resolve value on line 3 used to fail because it is 
    // processed before the datagroup 'value' is created
    @Test
    public void testQuery8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Secret public Object o; //@ in value; \n " +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" + // creates a datagroup named 'value'
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + 0;\n" + 
                "} \n"
        );
    }

    @Test
    public void testQuery8c() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  @Secret public int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" + // creates a datagroup named 'value'
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" + // OK - q is nested in value
                "  //@ @Secret public model Object o; in value; \n " +
                "} \n"
        );
    }

    // This test typechecks OK because the use of 'value' on line 3 is not resolved until after all Java declarations are
    // resolved - particularly value(), which will create the datagroup named value
    @Test
    public void testQuery8b() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret public int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" + // creates a datagroup named 'value'
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" + // OK - q is nested in value
                "} \n"
        );
    }

    @Test
    public void testQuery8OK() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret public int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret public Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" + // OK - q is nested in value
                "} \n"
        );
    }

    @Test
    public void testQuery8a() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  int f; @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(0) public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"org\") public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"value\",\"value\") public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"v\") public invariant true;\n" + // ERROR - not found
                "} \n"
                ,"/A.java:11: A secret annotation on an invariant must have exactly one argument",22
                ,"/A.java:12: incompatible types: int cannot be converted to java.lang.String",15
                ,"/A.java:13: cannot find symbol\n  symbol:   variable org\n  location: class A",15
                ,"/A.java:14: annotation values must be of the form 'name=value'",15
                ,"/A.java:14: annotation values must be of the form 'name=value'",23
                ,"/A.java:14: A secret annotation on an invariant must have exactly one argument",39
                ,"/A.java:15: cannot find symbol\n  symbol:   variable v\n  location: class A",15
        );
    }

    @Test
    public void testQuery9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model int value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret(\"value\") public int mm() { cache = null; q = 0; f = 0; }\n" +  // ERROR - can't write f; 
                "} \n"
                ,"/A.java:9: The field f is not writable since it is not in the value secret datagroup",59
        );
    }

    @Test
    public void testQuery10() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret model int value;\n" +
                "  //@ @Secret public model Object o; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret(\"value\") public int mm() {  q = 0;  }\n" +  // ERROR - can't read or write q
                "} \n"
                ,"/A.java:9: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",39
                ,"/A.java:9: The field q is not writable since it is not in the value secret datagroup",39
        );
    }

    @Test
    public void testQuery11() {
        helpTCF("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" +
                "  //@ @Secret model int value;\n" +
                "  //@ @Secret public model Object o; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret public void mm() {  }\n" +  // ERROR - methods must have a argument to @Secret
                "} \n"
                ,"/A.java:9: A secret annotation on a method must have exactly one argument",3
        );
    }

    // FIXME - what about secret invariants, represents clauses or initializers of secret fields
    // FIXME - what about reading from/writing to - selections and array references
    // FIXME - what about calling non-secret methods, constructors

}
