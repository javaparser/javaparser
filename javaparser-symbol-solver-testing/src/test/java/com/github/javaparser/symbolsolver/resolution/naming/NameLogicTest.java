package com.github.javaparser.symbolsolver.resolution.naming;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
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

public class NameLogicTest extends AbstractResolutionTest {

    private Node getNameInCode(String code, String name, ParseStart parseStart) {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_10);
        ParseResult<? extends Node> parseResult = new JavaParser(parserConfiguration).parse(parseStart, new StringProvider(code));
        if (!parseResult.isSuccessful()) {
            parseResult.getProblems().forEach(p -> System.out.println("ERR: " + p));
        }
        assertTrue(parseResult.isSuccessful());
        Node root = parseResult.getResult().get();
        List<Node> allNames = root.findAll(Node.class).stream()
                .filter(NameLogic::isAName)
                .collect(Collectors.toList());
        List<Node> matchingNames = allNames.stream()
                .filter(n -> NameLogic.nameAsString(n).equals(name))
                .collect(Collectors.toList());
        // In case of one name being contained in other as is, we remove it
        for (int i=0;i<matchingNames.size();i++) {
            Node container = matchingNames.get(i);
            for (int j=i+1;j<matchingNames.size();j++) {
                Node contained = matchingNames.get(j);
                if (contained.getParentNode().isPresent() && contained.getParentNode().get() == container
                    && NameLogic.nameAsString(contained).equals(NameLogic.nameAsString(container))) {
                    matchingNames.remove(j);
                    j--;
                }
            }
        }

        if (matchingNames.size() == 0) {
            throw new IllegalArgumentException("Not found. Names found: " + String.join(", ",
                    allNames.stream().map(NameLogic::nameAsString).collect(Collectors.toList())));
        } else if (matchingNames.size() > 1) {
            throw new IllegalArgumentException("Ambiguous: there are several matching.");
        } else {
            return matchingNames.get(0);
        }
    }

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
    public void annotationMemberTypeTypeName() {
        assertNameInCodeIsSyntactically("@interface MyAnno { bar.MyClass myMember(); }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void throwClauseMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void throwClauseConstructorTypeName() {
        assertNameInCodeIsSyntactically("class Foo { Foo() throws bar.MyClass {} }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void fieldTypeTypeName() {
        assertNameInCodeIsSyntactically("class Foo { bar.MyClass myField; }", "bar.MyClass",
                NameCategory.TYPE_NAME, ParseStart.COMPILATION_UNIT);
    }

    @Test
    public void formalParameterOfMethodTypeName() {
        assertNameInCodeIsSyntactically("class Foo { void myMethod(bar.MyClass param) {} }", "bar.MyClass",
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
    
}
