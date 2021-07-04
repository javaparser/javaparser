package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class matchClasses  extends TCBase {

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
    @Test public void testSimple() {
        helpTCF("$A/A.java",
                "public class A {  } class B {}");
    }
    
    @Test public void testDuplicate() {
        helpTCF("$A/A.java",
                "public class A {  } class A {}"
                ,"/$A/A.java:1: duplicate class: A",21
                );
    }
    
    @Test public void testModel() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model class B {} */"
                );
    }
    
    @Test public void testModelB() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ class B {}*/ "
                ,"/$A/A.java:1: A method or type declaration within a JML annotation must be model",25
                );
    }
    
    @Test public void testModelC() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model */ class B {}"
                ,"/$A/A.java:1: A Java declaration (not within a JML annotation) may not be either ghost or model",34
                );
    }
    
    @Test public void testModelDup() {
        helpTCF("$A/A.java",
                "public class A {  } /*@ model  class A {} */"
                // Changed for Java 8
                ,"/$A/A.java:1: duplicate class: A",32
                
//                ,"/$A/A.java:1: This specification declaration of type A has the same name as a previous JML type declaration",32
//                ,"/$A/A.java:1: Associated declaration: /$A/A.java:1: ",8
                );
    }

    @Test public void testJmlSimple() {
        addMockFile("$A/A.jml", "public class A {  } class B {}");
        helpTCF("$A/A.java",
                "public class A {  } class B {}");
    }
    
    @Test public void testJmlNoMatch() {
        addMockFile("$A/A.jml", "public class A {  } class B {}");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: This specification declaration of type B does not match any Java type declaration in /$A/A.java",21
                );
    }
    
    @Test public void testJmlExtra() {
        addMockFile("$A/A.jml", "public class A {  } ");
        helpTCF("$A/A.java",
                "public class A {  } class B {}"
                );
    }
    
    @Test public void testJmlDupIgnored() {
        addMockFile("$A/A.jml", "public class A {  } ");
        helpTCF("$A/A.java",
                "public class A {  } /*@ model class A {} */");
    }
    
    @Test public void testJmlDup() {
        addMockFile("$A/A.jml", "public class A {  } class A {}");
        helpTCF("$A/A.java",
                "  public class A {  } "
                // Changed for Java 8
                ,"/$A/A.jml:1: duplicate class: A",21
                
//                ,"/$A/A.jml:1: This specification declaration of type A has the same name as a previous JML type declaration",21
//                ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:1: ",8
                );
    }
    
    @Test public void testJmlDup2() {
        addMockFile("$A/A.jml", "public class A {  } \n/*@ model class A {} */");
        helpTCF("$A/A.java",
                "  public class A {  } "
                // Changed for Java 8
                ,"/$A/A.jml:2: duplicate class: A",11

//                ,"/$A/A.jml:2: This specification declaration of type A has the same name as a previous JML type declaration",11
//                ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",8
                );
    }
    
    @Test public void testJmlDup3() {
        addMockFile("$A/A.jml", "public class A {  } \n/*@ class A {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                // Changed for Java 8
                ,"/$A/A.jml:2: duplicate class: A",5

//                ,"/$A/A.jml:2: This specification declaration of type A has the same name as a previous JML type declaration",5
//                ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",8
                ); // FIXME - missing the missing model complaint
    }
    
    @Test public void testJmlMatch() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model class B {} */");
        helpTCF("$A/A.java",
                "  public class A {  } class B {}"
                ,"/$A/A.jml:1: A model type may not match a Java type declaration",31
                ,"/$A/A.java:1: Associated declaration: /$A/A.jml:1: ",23 
                );
    }
    
    @Test public void testJmlModel() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model class B {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                );
    }
    
    @Test public void testJmlModel2() {
        addMockFile("$A/A.jml", "public class A {  } /*@  class B {} */");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: A method or type declaration within a JML annotation must be model",26
                );
    }
    
    @Test public void testJmlModel3() {
        addMockFile("$A/A.jml", "public class A {  } /*@ model */ class B {} ");
        helpTCF("$A/A.java",
                "public class A {  } "
                ,"/$A/A.jml:1: This specification declaration of type B does not match any Java type declaration in /$A/A.java",34
                ,"/$A/A.jml:1: A Java declaration (not within a JML annotation) may not be either ghost or model",34
                );
    }
    
    @Test public void testSimpleField() {
        helpTCF("$A/A.java",
                "public class A { int j; } ");
    }
    
    @Test public void testSimpleFieldDup() {
        helpTCF("$A/A.java",
                "public class A { int j; int j; } "
                ,"/$A/A.java:1: variable j is already defined in class A",29
                );
    }
    
    @Test public void testSimpleFieldModelDup() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model int j; */ } "
                ,"/$A/A.java:2: variable j is already defined in class A",15
                );
    }
    
    @Test public void testSimpleFieldModelDup2() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model */ int j;} "
                ,"/$A/A.java:2: variable j is already defined in class A",18
                ,"/$A/A.java:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                );
    }
    
    @Test public void testSimpleFieldModelDup3() {
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@  int j; */} "
                ,"/$A/A.java:2: variable j is already defined in class A",10
                );
    }
    
    @Test public void testJmlSimpleField() {
        addMockFile("$A/A.jml", "public class A { int j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                );
    }
    
    @Test public void testJmlSimpleFieldTypeError() {
        addMockFile("$A/A.jml", "public class A { double j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: The field j in the specification matches a Java field A.j but they have different types: double vs. int",18
                ,"/$A/A.java:1: Associated declaration: /$A/A.jml:1: ",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup() {
        addMockFile("$A/A.jml", "public class A { /*@ model int j; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: variable j is already defined in class A",32
                );
    }
    
    @Test public void testJmlSimpleFieldDup2() {
        addMockFile("$A/A.jml", "public class A { int j; /*@ model int j; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: variable j is already defined in class A",39
                );
    }
    
    @Test public void testJmlSimpleFieldDup4() {
        addMockFile("$A/A.jml", "public class A { int j; \n/*@ model */ int j; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                ,"/$A/A.jml:2: This specification declaration of field j has the same name as a previous field declaration",18
                ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",22
                );
    }
    
    @Test public void testJmlSimpleFieldDup3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ int jjjj; */ }");
        helpTCF("$A/A.java",
                "public class A { int jjjj; } "
                ,"/$A/A.jml:2: variable jjjj is already defined in class A",9
                ,"/$A/A.jml:2: A declaration within a JML annotation must be either ghost or model",9
                ,"/$A/A.jml:2: A declaration within a JML annotation must be either ghost or model",9
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatch() {
        addMockFile("$A/A.jml", "public class A { int k; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: The field k is a Java field (neither ghost nor model) but does not match any fields in the corresponding Java class.",22
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatchOK() {
        addMockFile("$A/A.jml", "public class A { /*@ model int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                );
    }
    
    @Test public void testJmlSimpleFieldNoMatch2() {
        addMockFile("$A/A.jml", "public class A { /*@  int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: A declaration within a JML annotation must be either ghost or model",27
                ); // FIXME - missing the missing model complaint
    }
    
    @Test public void testJmlSimpleFieldNoMatch3() {
        addMockFile("$A/A.jml", "public class A { /*@ model */ int k; }");
        helpTCF("$A/A.java",
                "public class A { int j; } "
                ,"/$A/A.jml:1: A Java declaration (not within a JML annotation) may not be either ghost or model",22
                ,"/$A/A.jml:1: The field k is a Java field (neither ghost nor model) but does not match any fields in the corresponding Java class.",35
                );
    }
    
    @Test public void testSimpleMethod() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } ");
    }
    
    @Test public void testSimpleMethodDup() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} int j(){return 0;} } "
                ,"/$A/A.java:1: method j() is already defined in class A",41
                );
    }
    
    @Test public void testSimpleMethodModelDup() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ model int j(){return 0;}  */ } "
                ,"/$A/A.java:2: method j() is already defined in class A",15
                );
    }
    
    @Test public void testSimpleMethodModelDup2() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ model */ int j(){return 0;} } "
                ,"/$A/A.java:2: method j() is already defined in class A",18
                ,"/$A/A.java:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                );
    }
    
    @Test public void testSimpleMethodModelDup3() {
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  \n/*@ int j(){return 0;}  */} "
                ,"/$A/A.java:2: method j() is already defined in class A",9
                //,"/$A/A.java:2: A declaration within a JML annotation must be either ghost or model",9 // Duplicate ignored in Java 8
                );
    }
    
    @Test public void testJmlSimpleMethod() {
        addMockFile("$A/A.jml", "public class A { int j();  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                );
    }
    
    @Test public void testJmlSimpleMethodWithBody() {
        addMockFile("$A/A.jml", "public class A { int j(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: The specification of the method A.j() must not have a body",25
                );
    }
    
    @Test public void testJmlSimpleMethodTypeError() {
        addMockFile("$A/A.jml", "public class A { double j();  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: The return types of method A.j() are different in the specification and java files: double vs. int",18
// FIXME - should have an associated declaration
                );
    }
    
    @Test public void testJmlSimpleMethodTypeError2() {
        addMockFile("$A/A.jml", "public class A { int j(int k);  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: The method A.j(int) is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class.",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup() {
        addMockFile("$A/A.jml", "public class A { /*@ model int j(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: method j() is already defined in class A",32
                );
    }
    
    @Test public void testJmlSimpleMethodDup2() {
        addMockFile("$A/A.jml", "public class A { int j(); \n/*@ model int j(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: method j() is already defined in class A",15
                );
    }
    
    @Test public void testJmlSimpleMethodDup4() {
        addMockFile("$A/A.jml", "public class A { int j();  \n/*@ model */ int j(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } "
                ,"/$A/A.jml:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                ,"/$A/A.jml:2: Method j() is already defined in class A",18 
                ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",22
                );
    }
    
    @Test public void testJmlSimpleMethodDup5() {
        addMockFile("$A/A.jml", "public class A { int j();  \n/*@ model */ int j(int k){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} } "
                ,"/$A/A.jml:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                ,"/$A/A.jml:2: The method A.j(int) is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class.",18
                );
    }
    
    @Test public void testJmlSimpleMethodDup3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ int j();  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: method j() is already defined in class A",9
                //,"/$A/A.jml:2: A declaration within a JML annotation must be either ghost or model",9 // duplicate ignored in Java 8
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch() {
        addMockFile("$A/A.jml", "public class A { int k(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:1: The method A.k() is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class.",22
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatchOK() {
        addMockFile("$A/A.jml", "public class A { /*@ model int k();  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch2() {
        addMockFile("$A/A.jml", "public class A { \n/*@  int k(){return 0;}  */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: The specification of the method A.k() must not have a body",13 // Added for Java 8
                ,"/$A/A.jml:2: A method or type declaration within a JML annotation must be model",10 
                );
    }
    
    @Test public void testJmlSimpleMethodNoMatch3() {
        addMockFile("$A/A.jml", "public class A { \n/*@ model */ int k(){return 0;}  }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;}  } "
                ,"/$A/A.jml:2: A Java declaration (not within a JML annotation) may not be either ghost or model",5
                ,"/$A/A.jml:2: The method A.k() is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class.",18
                );
    }
    
    @Test public void testJmlMethodIgnored() {
        addMockFile("$A/A.jml", "public class A { \n/*@ model int k(){return 0;} */ }");
        helpTCF("$A/A.java",
                "public class A { int j(){return 0;} \n/*@ model int j(); */ } "
                );
    }
    
    @Test public void testJmlFieldIgnored() {
        addMockFile("$A/A.jml", "public class A { \n int j; /*@ model int k; */ }");
        helpTCF("$A/A.java",
                "public class A { int j; \n/*@ model int j; */ } "
                );
    }
    

    // FIXME - need all these corresponding tests for nested classes
}

