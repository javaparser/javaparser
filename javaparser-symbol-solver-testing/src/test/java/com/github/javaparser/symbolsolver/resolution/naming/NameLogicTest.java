package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.stmt.ReturnStmt;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.symbolsolver.resolution.naming.NameRole.DECLARATION;
import static com.github.javaparser.symbolsolver.resolution.naming.NameRole.REFERENCE;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class NameLogicTest extends AbstractNameLogicTest {


    private void assertNameInCodeIsSyntactically(String code, String name, NameCategory nameCategory, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertEquals(nameCategory, NameLogic.syntacticClassificationAccordingToContext(nameNode));
    }

    @Test
    void requiresModuleName() {
        assertNameInCodeIsSyntactically("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "java.xml", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void exportsModuleName() {
        assertNameInCodeIsSyntactically("module my.module{\n" +
                "  exports my.packag to other.module, another.module;\n" +
                "}", "other.module", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void opensModuleName() {
        assertNameInCodeIsSyntactically("module client.modul{\n" +
                "    opens some.client.packag to framework.modul;\n" +
                "    requires framework.modul2;\n" +
                "}", "framework.modul", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void exportsPackageName() {
        assertNameInCodeIsSyntactically("module common.widget{\n" +
                "  exports com.logicbig;\n" +
                "}", "com.logicbig", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void opensPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example.bar", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void packageNameInPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void usesTypeName() {
        assertNameInCodeIsSyntactically("module modi.mod {\n" +
                "    uses modi.api;\n" +
                "}", "modi.api", NameCategory.TYPE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void providesTypeName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    provides com.modi.api.query.Query with ModuleQuery;\n" +
                "}", "com.modi.api.query.Query", NameCategory.TYPE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void singleTypeImportTypeName() {
        assertNameInCodeIsSyntactically("import a.b.c;", "a.b.c",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void singleStaticTypeImportTypeName() {
        assertNameInCodeIsSyntactically("import static a.B.c;", "a.B",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void singleStaticImportOnDemandTypeName() {
        assertNameInCodeIsSyntactically("import static a.B.*;", "a.B",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void constructorDeclarationTypeName() {
        assertNameInCodeIsSyntactically("A() { }", "A",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void annotationTypeName() {
        assertNameInCodeIsSyntactically("@Anno class A {} ", "Anno",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classLiteralTypeName() {
        assertNameInCodeIsSyntactically("Class<?> c = String.class;", "String",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    void thisExprTypeName() {
        assertNameInCodeIsSyntactically("Object o = String.this;", "String",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    void qualifiedSuperFieldAccessTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super.myField;", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    void qualifiedSuperCallTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super.myCall();", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    void qualifiedSuperMethodReferenceTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super::myMethod;", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    void extendsClauseTypeName() {
        assertNameInCodeIsSyntactically("class Foo extends bar.MyClass { }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void implementsClauseTypeName() {
        assertNameInCodeIsSyntactically("class Foo implements bar.MyClass { }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void returnTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { bar.MyClass myMethod() {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void qualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeIsSyntactically("@interface MyAnno { bar.MyClass myMember(); }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void unqualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeIsSyntactically("@interface MyAnno { MyClass myMember(); }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void throwClauseMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void qualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeIsSyntactically("class Foo { Foo() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void unualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeIsSyntactically("class Foo { Foo() throws MyClass {} }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void qualifiedFieldTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { bar.MyClass myField; }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void fieldTypeTypeNameSecondAttempt() {
        assertNameInCodeIsSyntactically("public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {\n" +
                        "private TypeSolver typeSolver; }", "TypeSolver",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void unqualifiedFieldTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { MyClass myField; }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void qualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod(bar.MyClass param) {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void unqualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod(MyClass param) {} }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void receiverParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("void myMethod(Foo this) {}", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void variableDeclarationTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Foo myVar; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void exceptionParameterTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { try { } catch(Foo e) { } }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void explicitParameterTypeInConstructorCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Call<Foo>(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void explicitParameterTypeInMethodCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Call().<Foo>myMethod(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void instantiationCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void instantiationCallOfAnonymousTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo() { void method() { } } ; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void arrayCreationExpressionTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo[0]; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void castTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Object o = (Foo)someField; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void instanceOfTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { if (myValue instanceof Foo) { }; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void methodReferenceTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Object o = Foo::myMethod; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void qualifiedConstructorSuperClassInvocationExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression.super(); } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void qualifiedClassInstanceCreationExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression.new MyClass(); } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void arrayReferenceExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression[0]; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void postfixExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression++; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void leftHandAssignmentExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression = 2; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void variableAccessInTryWithResourceExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { try (anExpression) { }; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void variableAccessInTryWithResourceWothTypeExpressionName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void methodInvocationMethodName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { myMethod(); } } ", "myMethod",
                NameCategory.METHOD_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void leftOfQualifiedTypeNamePackageOrTypeName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path.to",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void typeImportOnDemandPackageOrTypeName() {
        assertNameInCodeIsSyntactically("import a.B.*;", "a.B",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void leftOfExpressionNameAmbiguousName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b.c",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void leftOfMethodCallAmbiguousName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.aMethod(); } } ", "a.b.c",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
    }



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
    void identifyNamesInSimpleExamples() {
        String code = "package a.b.c; class A { void foo(int param) { return a.b.c.D.e; } }";
        CompilationUnit cu = StaticJavaParser.parse(code);

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
    void identifyNameRolesInSimpleExamples() {
        String code = "package a.b.c; class A { void foo(int param) { return a.b.c.D.e; } }";
        CompilationUnit cu = StaticJavaParser.parse(code);

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
    void nameAsStringModuleName() {
        ModuleDeclaration md = parse("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", ParseStart.MODULE_DECLARATION);
        assertEquals("com.mydeveloperplanet.jpmshello", NameLogic.nameAsString(md.getName()));
    }

    @Test
    void nameAsStringClassName() {
        CompilationUnit cu = parse("class Foo extends bar.MyClass { }", ParseStart.COMPILATION_UNIT);
        assertEquals("Foo", NameLogic.nameAsString(cu.getType(0).getName()));
    }

    @Test
    void qualifiedModuleName() {
        assertIsQualifiedName("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "com.mydeveloperplanet.jpmshello", ParseStart.MODULE_DECLARATION);
    }

    @Test
    void simpleNameUnqualifiedAnnotationMemberTypeTypeName() {
        assertIsSimpleName("@interface MyAnno { MyClass myMember(); }", "MyClass",
                ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleModuleName() {
        assertNameInCodeHasRole("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "com.mydeveloperplanet.jpmshello", DECLARATION, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleRequiresModuleName() {
        assertNameInCodeHasRole("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "java.xml", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleExportsModuleName() {
        assertNameInCodeHasRole("module my.module{\n" +
                "  exports my.packag to other.module, another.module;\n" +
                "}", "other.module", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleOpensModuleName() {
        assertNameInCodeHasRole("module client.modul{\n" +
                "    opens some.client.packag to framework.modul;\n" +
                "    requires framework.modul2;\n" +
                "}", "framework.modul", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleExportsPackageName() {
        assertNameInCodeHasRole("module common.widget{\n" +
                "  exports com.logicbig;\n" +
                "}", "com.logicbig", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleOpensPackageName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example.bar", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRolePackageNameInPackageName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleUsesTypeName() {
        assertNameInCodeHasRole("module modi.mod {\n" +
                "    uses modi.api;\n" +
                "}", "modi.api", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleProvidesTypeName() {
        assertNameInCodeHasRole("module foo {\n" +
                "    provides com.modi.api.query.Query with ModuleQuery;\n" +
                "}", "com.modi.api.query.Query", REFERENCE, ParseStart.MODULE_DECLARATION);
    }

    @Test
    void classifyRoleSingleTypeImportTypeName() {
        assertNameInCodeHasRole("import a.b.c;", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleSingleStaticTypeImportTypeName() {
        assertNameInCodeHasRole("import static a.B.c;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleSingleStaticImportOnDemandTypeName() {
        assertNameInCodeHasRole("import static a.B.*;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleConstructorDeclarationTypeName() {
        assertNameInCodeHasRole("A() { }", "A",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleAnnotationTypeName() {
        assertNameInCodeHasRole("@Anno class A {} ", "Anno",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleClassName() {
        assertNameInCodeHasRole("@Anno class A {} ", "A",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleClassLiteralTypeName() {
        assertNameInCodeHasRole("Class<?> c = String.class;", "String",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    void classifyRoleThisExprTypeName() {
        assertNameInCodeHasRole("Object o = String.this;", "String",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    void classifyRoleQualifiedSuperFieldAccessTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super.myField;", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    void classifyRoleQualifiedSuperCallTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super.myCall();", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    void classifyRoleQualifiedSuperMethodReferenceTypeName() {
        assertNameInCodeHasRole("Object o = MyClass.super::myMethod;", "MyClass",
                REFERENCE, ParseStart.STATEMENT);
    }

    @Test
    void classifyRoleExtendsClauseTypeName() {
        assertNameInCodeHasRole("class Foo extends bar.MyClass { }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleImplementsClauseTypeName() {
        assertNameInCodeHasRole("class Foo implements bar.MyClass { }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleReturnTypeTypeName() {
        assertNameInCodeHasRole("class Foo { bar.MyClass myMethod() {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleQualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeHasRole("@interface MyAnno { bar.MyClass myMember(); }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleAnnotationName() {
        assertNameInCodeHasRole("@interface MyAnno { bar.MyClass myMember(); }", "MyAnno",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleUnqualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeHasRole("@interface MyAnno { MyClass myMember(); }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleThrowClauseMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod() throws bar.MyClass {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleQualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeHasRole("class Foo { Foo() throws bar.MyClass {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleUnualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeHasRole("class Foo { Foo() throws MyClass {} }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleQualifiedFieldTypeTypeName() {
        assertNameInCodeHasRole("class Foo { bar.MyClass myField; }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleFieldTypeTypeNameSecondAttempt() {
        assertNameInCodeHasRole("public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {\n" +
                        "private TypeSolver typeSolver; }", "TypeSolver",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleUnqualifiedFieldTypeTypeName() {
        assertNameInCodeHasRole("class Foo { MyClass myField; }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleFieldName() {
        assertNameInCodeHasRole("class Foo { MyClass myField; }", "myField",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleQualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod(bar.MyClass param) {} }", "bar.MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleUnqualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeHasRole("class Foo { void myMethod(MyClass param) {} }", "MyClass",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleMethodName() {
        assertNameInCodeHasRole("class Foo { void myMethod(MyClass param) {} }", "myMethod",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleReceiverParameterOfMethodTypeName() {
        assertNameInCodeHasRole("void myMethod(Foo this) {}", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleVariableDeclarationTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { Foo myVar; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleExceptionParameterTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { try { } catch(Foo e) { } }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleExceptionParameterName() {
        assertNameInCodeHasRole("void myMethod() { try { } catch(Foo e) { } }", "e",
                DECLARATION, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleExplicitParameterTypeInConstructorCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Call<Foo>(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleExplicitParameterTypeInMethodCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Call().<Foo>myMethod(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleInstantiationCallTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo(); }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleInstantiationCallOfAnonymousTypeTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo() { void method() { } } ; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleArrayCreationExpressionTypeName() {
        assertNameInCodeHasRole("void myMethod() { new Foo[0]; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleCastTypeName() {
        assertNameInCodeHasRole("void myMethod() { Object o = (Foo)someField; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleInstanceOfTypeName() {
        assertNameInCodeHasRole("void myMethod() { if (myValue instanceof Foo) { }; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleMethodReferenceTypeName() {
        assertNameInCodeHasRole("void myMethod() { Object o = Foo::myMethod; }", "Foo",
                REFERENCE, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleQualifiedConstructorSuperClassInvocationExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression.super(); } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleQualifiedClassInstanceCreationExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression.new MyClass(); } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleArrayReferenceExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression[0]; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRolePostfixExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression++; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleLeftHandAssignmentExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { anExpression = 2; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleVariableAccessInTryWithResourceExpressionName() {
        assertNameInCodeHasRole("class Bar { Bar() { try (anExpression) { }; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleVariableAccessInTryWithResourceWithTypeExpressionName() {
        assertNameInCodeHasRole("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "anExpression",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyTryWithResourceName() {
        assertNameInCodeHasRole("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "o",
                DECLARATION, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleMethodInvocationMethodName() {
        assertNameInCodeHasRole("class Bar {  Bar() { myMethod(); } } ", "myMethod",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleLeftOfQualifiedTypeNamePackageOrTypeName() {
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path.to",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleTypeImportOnDemandPackageOrTypeName() {
        assertNameInCodeHasRole("import a.B.*;", "a.B",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleLeftOfExpressionNameAmbiguousName() {
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b",
                REFERENCE, ParseStart.COMPILATION_UNIT);
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void classifyRoleLeftOfMethodCallAmbiguousName() {
        assertNameInCodeHasRole("class Bar { Bar() { a.b.c.aMethod(); } } ", "a.b.c",
                REFERENCE, ParseStart.COMPILATION_UNIT);
    }

    @Test
    void defaultValueTypeName() {
        assertNameInCodeIsSyntactically("@RequestForEnhancement(\n" +
                        "    id       = 2868724,\n" +
                        "    synopsis = \"Provide time-travel functionality\",\n" +
                        "    engineer = \"Mr. Peabody\",\n" +
                        "    date     = anExpression" +
                        ")\n" +
                        "public static void travelThroughTime(Date destination) {  }",
                "anExpression", NameCategory.AMBIGUOUS_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    void classifyRoleDefaultValueTypeName() {
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
    void classifyRoleDefaultValueDeclaration() {
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
