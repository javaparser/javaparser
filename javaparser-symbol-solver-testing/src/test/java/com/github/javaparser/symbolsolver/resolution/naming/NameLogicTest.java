package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.stmt.ReturnStmt;
import org.junit.Test;

import static com.github.javaparser.symbolsolver.resolution.naming.NameRole.DECLARATION;
import static com.github.javaparser.symbolsolver.resolution.naming.NameRole.REFERENCE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class NameLogicTest extends AbstractNameLogicTest {

    private void assertNameInCodeHasRole(String code, String name, NameRole nameRole, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertEquals(nameRole, NameLogic.classifyRole(nameNode));
    }

    private void assertIsSimpleName(String code, String name, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertTrue(NameLogic.isSimpleName(nameNode));
    }

    private void assertIsQualifiedName(String code, String name, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertTrue(NameLogic.isQualifiedName(nameNode));
    }

    @Test
    public void identifyNamesInSimpleExamples() {
        String code = "package a.b.c; class A { void foo(int param) { return a.b.c.D.e; } }";
        CompilationUnit cu = JavaParser.parse(code);

        assertEquals(false, NameLogic.isAName(cu));
        assertEquals(false, NameLogic.isAName(cu.getPackageDeclaration().get()));

        Name packageName = cu.getPackageDeclaration().get().getName();
        assertEquals(true, NameLogic.isAName(packageName));
        assertEquals(true, NameLogic.isAName(packageName.getQualifier().get()));
        assertEquals(true, NameLogic.isAName(packageName.getQualifier().get().getQualifier().get()));

        ClassOrInterfaceDeclaration classA = cu.getType(0).asClassOrInterfaceDeclaration();
        assertEquals(false, NameLogic.isAName(classA));
        assertEquals(true, NameLogic.isAName(classA.getName()));

        MethodDeclaration methodFoo = classA.getMethods().get(0);
        assertEquals(false, NameLogic.isAName(methodFoo));
        assertEquals(true, NameLogic.isAName(methodFoo.getName()));
        assertEquals(false, NameLogic.isAName(methodFoo.getParameter(0)));
        assertEquals(true, NameLogic.isAName(methodFoo.getParameter(0).getName()));
        assertEquals(false, NameLogic.isAName(methodFoo.getParameter(0).getType()));
        assertEquals(false, NameLogic.isAName(methodFoo.getType()));

        ReturnStmt returnStmt = methodFoo.getBody().get().getStatements().get(0).asReturnStmt();
        assertEquals(false, NameLogic.isAName(returnStmt));
        assertEquals(true, NameLogic.isAName(returnStmt.getExpression().get()));
        FieldAccessExpr fieldAccessExpr = returnStmt.getExpression().get().asFieldAccessExpr();
        assertEquals(true, NameLogic.isAName(fieldAccessExpr
                .getScope())); // a.b.c.D
        assertEquals(true, NameLogic.isAName(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope())); // a.b.c
        assertEquals(true, NameLogic.isAName(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope())); // a.b
        assertEquals(true, NameLogic.isAName(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope())); // a
    }

    @Test
    public void identifyNameRolesInSimpleExamples() {
        String code = "package a.b.c; class A { void foo(int param) { return a.b.c.D.e; } }";
        CompilationUnit cu = JavaParser.parse(code);

        Name packageName = cu.getPackageDeclaration().get().getName();
        assertEquals(DECLARATION, NameLogic.classifyRole(packageName));
        assertEquals(DECLARATION, NameLogic.classifyRole(packageName.getQualifier().get()));
        assertEquals(DECLARATION, NameLogic.classifyRole(packageName.getQualifier().get().getQualifier().get()));

        ClassOrInterfaceDeclaration classA = cu.getType(0).asClassOrInterfaceDeclaration();
        assertEquals(DECLARATION, NameLogic.classifyRole(classA.getName()));

        MethodDeclaration methodFoo = classA.getMethods().get(0);
        assertEquals(DECLARATION, NameLogic.classifyRole(methodFoo.getName()));
        assertEquals(DECLARATION, NameLogic.classifyRole(methodFoo.getParameter(0).getName()));

        ReturnStmt returnStmt = methodFoo.getBody().get().getStatements().get(0).asReturnStmt();
        assertEquals(REFERENCE, NameLogic.classifyRole(returnStmt.getExpression().get())); // a.b.c.D.e
        FieldAccessExpr fieldAccessExpr = returnStmt.getExpression().get().asFieldAccessExpr();
        assertEquals(REFERENCE, NameLogic.classifyRole(fieldAccessExpr
                .getScope())); // a.b.c.D
        assertEquals(REFERENCE, NameLogic.classifyRole(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope())); // a.b.c
        assertEquals(REFERENCE, NameLogic.classifyRole(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope())); // a.b
        assertEquals(REFERENCE, NameLogic.classifyRole(fieldAccessExpr
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope().asFieldAccessExpr()
                .getScope())); // a
    }

    @Test
    public void nameAsStringModuleName() {
        ModuleDeclaration md = parse("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", ParseStart.MODULE_DECLARATION);
        assertEquals("com.mydeveloperplanet.jpmshello", NameLogic.nameAsString(md.getName()));
    }

    @Test
    public void nameAsStringClassName() {
        CompilationUnit cu = parse("class Foo extends bar.MyClass { }", ParseStart.COMPILATION_UNIT);
        assertEquals("Foo", NameLogic.nameAsString(cu.getType(0).getName()));
    }

    @Test
    public void qualifiedModuleName() {
        assertIsQualifiedName("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "com.mydeveloperplanet.jpmshello", ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void simpleNameUnqualifiedAnnotationMemberTypeTypeName() {
        assertIsSimpleName("@interface MyAnno { MyClass myMember(); }", "MyClass",
                ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleModuleName() {
        assertNameInCodeHasRole("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "com.mydeveloperplanet.jpmshello", DECLARATION, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleRequiresModuleName() {
        assertNameInCodeHasRole("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "java.xml", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleExportsModuleName() {
        assertNameInCodeHasRole("module my.module{\n" +
                "  exports my.packag to other.module, another.module;\n" +
                "}", "other.module", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleOpensModuleName() {
        assertNameInCodeHasRole("module client.modul{\n" +
                "    opens some.client.packag to framework.modul;\n" +
                "    requires framework.modul2;\n" +
                "}", "framework.modul", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleExportsPackageName() {
        assertNameInCodeHasRole("module common.widget{\n" +
                "  exports com.logicbig;\n" +
                "}", "com.logicbig", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleOpensPackageName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example.bar", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRolePackageNameInPackageName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleUsesTypeName() {
        assertNameInCodeHasRole("module modi.mod {\n" +
                "    uses modi.api;\n" +
                "}", "modi.api", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleProvidesTypeName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    provides com.modi.api.query.Query with ModuleQuery;\n" +
                "}", "com.modi.api.query.Query", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void classifyRoleSingleTypeImportTypeName() {
        assertNameInCodeHasRole("import a.b.c;", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleSingleStaticTypeImportTypeName() {
        assertNameInCodeHasRole("import static a.B.c;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleSingleStaticImportOnDemandTypeName() {
        assertNameInCodeHasRole("import static a.B.*;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleConstructorDeclarationTypeName() {
        assertNameInCodeHasRole("A() { }", "A",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleAnnotationTypeName() {
        assertNameInCodeHasRole("@Anno class A {} ", "Anno",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleClassName() {
        assertNameInCodeHasRole("@Anno class A {} ", "A",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleClassLiteralTypeName() {
        assertNameInCodeHasRole("Class<?> c = String.class;", "String",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    public void classifyRoleThisExprTypeName() {
        assertNameInCodeHasRole("Object o = String.this;", "String",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    public void classifyRoleQualifiedSuperFieldAccessTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super.myField;", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    public void classifyRoleQualifiedSuperCallTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super.myCall();", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    public void classifyRoleQualifiedSuperMethodReferenceTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super::myMethod;", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    public void classifyRoleExtendsClauseTypeName() {
        assertNameInCodeHasRole("class Foo extends bar.MyClass { }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleImplementsClauseTypeName() {
        assertNameInCodeHasRole("class Foo implements bar.MyClass { }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleReturnTypeTypeName() {
        assertNameInCodeHasRole("class Foo { bar.MyClass myMethod() {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleQualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeHasRole("@interface MyAnno { bar.MyClass myMember(); }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleAnnotationName() {
        assertNameInCodeHasRole("@interface MyAnno { bar.MyClass myMember(); }", "MyAnno",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleUnqualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeHasRole("@interface MyAnno { MyClass myMember(); }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleThrowClauseMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod() throws bar.MyClass {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleQualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeHasRole("class Foo { Foo() throws bar.MyClass {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleUnualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeHasRole("class Foo { Foo() throws MyClass {} }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleQualifiedFieldTypeTypeName() {
        assertNameInCodeHasRole("class Foo { bar.MyClass myField; }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleFieldTypeTypeNameSecondAttempt() {
        assertNameInCodeHasRole("public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {\n" +
                        "private TypeSolver typeSolver; }", "TypeSolver",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleUnqualifiedFieldTypeTypeName() {
        assertNameInCodeHasRole("class Foo { MyClass myField; }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleFieldName() {
        assertNameInCodeHasRole("class Foo { MyClass myField; }", "myField",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleQualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod(bar.MyClass param) {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleUnqualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod(MyClass param) {} }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleMethodName() {
        assertNameInCodeHasRole("class Foo { void myMethod(MyClass param) {} }", "myMethod",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleReceiverParameterOfMethodTypeName() {
        assertNameInCodeHasRole("void myMethod(Foo this) {}", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleVariableDeclarationTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { Foo myVar; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleExceptionParameterTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { try { } catch(Foo e) { } }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleExceptionParameterName() {
        assertNameInCodeHasRole("void myMethod() { try { } catch(Foo e) { } }", "e",
                DECLARATION, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleExplicitParameterTypeInConstructorCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Call<Foo>(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleExplicitParameterTypeInMethodCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Call().<Foo>myMethod(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleInstantiationCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleInstantiationCallOfAnonymousTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo() { void method() { } } ; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleArrayCreationExpressionTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo[0]; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleCastTypeName() {
        assertNameInCodeHasRole("void myMethod() { Object o = (Foo)someField; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleInstanceOfTypeName() {
        assertNameInCodeHasRole("void myMethod() { if (myValue instanceof Foo) { }; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleMethodReferenceTypeName() {
        assertNameInCodeHasRole("void myMethod() { Object o = Foo::myMethod; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleQualifiedConstructorSuperClassInvocationExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression.super(); } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleQualifiedClassInstanceCreationExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression.new MyClass(); } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleArrayReferenceExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression[0]; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRolePostfixExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression++; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleLeftHandAssignmentExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression = 2; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleVariableAccessInTryWithResourceExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { try (anExpression) { }; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleVariableAccessInTryWithResourceWithTypeExpressionName() {
        assertNameInCodeHasRole("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyTryWithResourceName() {
        assertNameInCodeHasRole("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "o",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleMethodInvocationMethodName() {
        assertNameInCodeHasRole("class Bar {  Bar() { myMethod(); } } ", "myMethod",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleLeftOfQualifiedTypeNamePackageOrTypeName() {
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path.to",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleTypeImportOnDemandPackageOrTypeName() {
        assertNameInCodeHasRole("import a.B.*;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleLeftOfExpressionNameAmbiguousName() {
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleLeftOfMethodCallAmbiguousName() {
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.aMethod(); } } ", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classifyRoleDefaultValueTypeName() {
        assertNameInCodeHasRole("@RequestForEnhancement(\n" +
                        "    id       = 2868724,\n" +
                        "    synopsis = \"Provide time-travel functionality\",\n" +
                        "    engineer = \"Mr. Peabody\",\n" +
                        "    date     = anExpression" +
                        ")\n" +
                        "public static void travelThroughTime(Date destination) {  }",
                "anExpression", REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    public void classifyRoleDefaultValueDeclaration() {
        assertNameInCodeHasRole("@RequestForEnhancement(\n" +
                        "    id       = 2868724,\n" +
                        "    synopsis = \"Provide time-travel functionality\",\n" +
                        "    engineer = \"Mr. Peabody\",\n" +
                        "    date     = anExpression" +
                        ")\n" +
                        "public static void travelThroughTime(Date destination) {  }",
                "date", DECLARATION, ParseStart.CLASS_BODY);
    }
    
}
