package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class NameLogicTest extends AbstractNameLogicTest {



    private void assertNameInCodeIsSyntactically(String code, String name, NameCategory nameCategory, ParseStart parseStart) {
        Node nameNode = getNameInCode(code, name, parseStart);
        assertEquals(nameCategory, NameLogic.syntacticClassificationAccordingToContext(nameNode));
    }

    @Test
    public void requiresModuleName() {
        assertNameInCodeIsSyntactically("module com.mydeveloperplanet.jpmshello {\n" +
                "    requires java.base;\n" +
                "    requires java.xml;\n" +
                "    requires com.mydeveloperplanet.jpmshi;\n" +
                "}\n", "java.xml", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void exportsModuleName() {
        assertNameInCodeIsSyntactically("module my.module{\n" +
                "  exports my.packag to other.module, another.module;\n" +
                "}", "other.module", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void opensModuleName() {
        assertNameInCodeIsSyntactically("module client.modul{\n" +
                "    opens some.client.packag to framework.modul;\n" +
                "    requires framework.modul2;\n" +
                "}", "framework.modul", NameCategory.MODULE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void exportsPackageName() {
        assertNameInCodeIsSyntactically("module common.widget{\n" +
                "  exports com.logicbig;\n" +
                "}", "com.logicbig", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void opensPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example.bar", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void packageNameInPackageName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    opens com.example.bar;\n" +
                "}", "com.example", NameCategory.PACKAGE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void usesTypeName() {
        assertNameInCodeIsSyntactically("module modi.mod {\n" +
                "    uses modi.api;\n" +
                "}", "modi.api", NameCategory.TYPE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void providesTypeName() {
        assertNameInCodeIsSyntactically("module foo {\n" +
                "    provides com.modi.api.query.Query with ModuleQuery;\n" +
                "}", "com.modi.api.query.Query", NameCategory.TYPE_NAME, ParseStart.MODULE_DECLARATION);
    }

    @Test
    public void singleTypeImportTypeName() {
        assertNameInCodeIsSyntactically("import a.b.c;", "a.b.c",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void singleStaticTypeImportTypeName() {
        assertNameInCodeIsSyntactically("import static a.B.c;", "a.B",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void singleStaticImportOnDemandTypeName() {
        assertNameInCodeIsSyntactically("import static a.B.*;", "a.B",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void constructorDeclarationTypeName() {
        assertNameInCodeIsSyntactically("A() { }", "A",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void annotationTypeName() {
        assertNameInCodeIsSyntactically("@Anno class A {} ", "Anno",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void classLiteralTypeName() {
        assertNameInCodeIsSyntactically("Class<?> c = String.class;", "String",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    public void thisExprTypeName() {
        assertNameInCodeIsSyntactically("Object o = String.this;", "String",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    public void qualifiedSuperFieldAccessTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super.myField;", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    public void qualifiedSuperCallTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super.myCall();", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    public void qualifiedSuperMethodReferenceTypeName() {
        assertNameInCodeIsSyntactically("Object o = MyClass.super::myMethod;", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.STATEMENT);
    }

    @Test
    public void extendsClauseTypeName() {
        assertNameInCodeIsSyntactically("class Foo extends bar.MyClass { }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void implementsClauseTypeName() {
        assertNameInCodeIsSyntactically("class Foo implements bar.MyClass { }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void returnTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { bar.MyClass myMethod() {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void qualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeIsSyntactically("@interface MyAnno { bar.MyClass myMember(); }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void unqualifiedAnnotationMemberTypeTypeName() {
        assertNameInCodeIsSyntactically("@interface MyAnno { MyClass myMember(); }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void throwClauseMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void qualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeIsSyntactically("class Foo { Foo() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void unualifiedThrowClauseConstructorTypeName() {
        assertNameInCodeIsSyntactically("class Foo { Foo() throws MyClass {} }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void qualifiedFieldTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { bar.MyClass myField; }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void fieldTypeTypeNameSecondAttempt() {
        assertNameInCodeIsSyntactically("public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements InterfaceDeclaration {\n" +
                        "private TypeSolver typeSolver; }", "TypeSolver",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void unqualifiedFieldTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { MyClass myField; }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void qualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod(bar.MyClass param) {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void unqualifiedFormalParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod(MyClass param) {} }", "MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void receiverParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("void myMethod(Foo this) {}", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void variableDeclarationTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Foo myVar; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void exceptionParameterTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { try { } catch(Foo e) { } }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void explicitParameterTypeInConstructorCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Call<Foo>(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void explicitParameterTypeInMethodCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Call().<Foo>myMethod(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void instantiationCallTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo(); }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void instantiationCallOfAnonymousTypeTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo() { void method() { } } ; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void arrayCreationExpressionTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { new Foo[0]; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void castTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Object o = (Foo)someField; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void instanceOfTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { if (myValue instanceof Foo) { }; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void methodReferenceTypeName() {
        assertNameInCodeIsSyntactically("void myMethod() { Object o = Foo::myMethod; }", "Foo",
                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
    }

    @Test
    public void qualifiedConstructorSuperClassInvocationExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression.super(); } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void qualifiedClassInstanceCreationExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression.new MyClass(); } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void arrayReferenceExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression[0]; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void postfixExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression++; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void leftHandAssignmentExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { anExpression = 2; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void variableAccessInTryWithResourceExpressionName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { try (anExpression) { }; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void variableAccessInTryWithResourceWothTypeExpressionName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { try (Object o = anExpression) { }; } } ", "anExpression",
                NameCategory.EXPRESSION_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void methodInvocationMethodName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { myMethod(); } } ", "myMethod",
                NameCategory.METHOD_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void leftOfQualifiedTypeNamePackageOrTypeName() {
        assertNameInCodeIsSyntactically("class Bar {  Bar() { new myQualified.path.to.TypeName(); } } ", "myQualified.path.to",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void typeImportOnDemandPackageOrTypeName() {
        assertNameInCodeIsSyntactically("import a.B.*;", "a.B",
                NameCategory.PACKAGE_OR_TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void leftOfExpressionNameAmbiguousName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b.c",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a.b",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.anExpression[0]; } } ", "a",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void leftOfMethodCallAmbiguousName() {
        assertNameInCodeIsSyntactically("class Bar { Bar() { a.b.c.aMethod(); } } ", "a.b.c",
                NameCategory.AMBIGUOUS_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void defaultValueTypeName() {
        assertNameInCodeIsSyntactically("@RequestForEnhancement(\n" +
                        "    id       = 2868724,\n" +
                        "    synopsis = \"Provide time-travel functionality\",\n" +
                        "    engineer = \"Mr. Peabody\",\n" +
                        "    date     = anExpression" +
                        ")\n" +
                        "public static void travelThroughTime(Date destination) {  }",
                "anExpression", NameCategory.AMBIGUOUS_NAME, ParseStart.CLASS_BODY);
    }

    // TODO unclear reading the JLS
//    @Test
//    public void methodReferenceAmbiguousName() {
//        assertNameInCodeIsSyntactically("void myMethod() { Object o = a.b.c.Foo::myMethod; }", "a.b.c.Foo",
//                NameCategory.TYPE_NAME, ParseStart.CLASS_BODY);
//        assertNameInCodeIsSyntactically("void myMethod() { Object o = a.b.c.Foo::myMethod; }", "a.b.c",
//                NameCategory.AMBIGUOUS_NAME, ParseStart.CLASS_BODY);
//        assertNameInCodeIsSyntactically("void myMethod() { Object o = a.b.c.Foo::myMethod; }", "a.b",
//                NameCategory.AMBIGUOUS_NAME, ParseStart.CLASS_BODY);
//        assertNameInCodeIsSyntactically("void myMethod() { Object o = a.b.c.Foo::myMethod; }", "a",
//                NameCategory.AMBIGUOUS_NAME, ParseStart.CLASS_BODY);
//    }
    
}
