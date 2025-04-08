/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.StaticJavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter.NODE_TEXT_DATA;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.utils.LineSeparator;
import com.github.javaparser.utils.TestUtils;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;

class LexicalPreservingPrinterTest extends AbstractLexicalPreservingTest {
    private NodeText getTextForNode(Node node) {
        return node.getData(NODE_TEXT_DATA);
    }

    //
    // Tests on TextNode definition
    //

    @Test
    void checkNodeTextCreatedForSimplestClass() {
        considerCode("class A {}");

        // CU
        assertEquals(1, getTextForNode(cu).numberOfElements());
        assertTrue(getTextForNode(cu).getTextElement(0) instanceof ChildTextElement);
        assertEquals(
                cu.getClassByName("A").get(),
                ((ChildTextElement) getTextForNode(cu).getTextElement(0)).getChild());

        // Class
        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        assertEquals(7, getTextForNode(classA).numberOfElements());
        assertEquals("class", getTextForNode(classA).getTextElement(0).expand());
        assertEquals(" ", getTextForNode(classA).getTextElement(1).expand());
        assertEquals("A", getTextForNode(classA).getTextElement(2).expand());
        assertEquals(" ", getTextForNode(classA).getTextElement(3).expand());
        assertEquals("{", getTextForNode(classA).getTextElement(4).expand());
        assertEquals("}", getTextForNode(classA).getTextElement(5).expand());
        assertEquals("", getTextForNode(classA).getTextElement(6).expand());
        assertTrue(getTextForNode(classA).getTextElement(6) instanceof TokenTextElement);
        assertEquals(
                GeneratedJavaParserConstants.EOF,
                ((TokenTextElement) getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(fd);
        assertEquals(
                Arrays.asList("int", " ", "i", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForVariableDeclarator() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        VariableDeclarator vd = fd.getVariables().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(vd);
        assertEquals(
                Arrays.asList("i"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(
                Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethodParameter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(p1);
        assertEquals(
                Arrays.asList("int", " ", "p1"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethodParameterWithAnnotation() {
        String code = "class A {void foo(@Nullable String p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(p1);
        assertEquals(
                Arrays.asList("@Nullable", " ", "String", " ", "p1"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethodWithTypeArgument() {
        String code = "class A {Set<String> foo(String p1, float p2) { return null;}}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Type p1 = md.getType().asClassOrInterfaceType().getTypeArguments().get().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(p1);
        assertEquals(
                Arrays.asList("String"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethodWithAnnotatedTypeArgument() {
        String code = "class A {Set<@Nullable String> foo() { return null;}}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Type p1 = md.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(p1);
        assertEquals(
                Arrays.asList("Set", "<", "@", "Nullable", " ", "String", ">"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForPrimitiveType() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        Type t = p1.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(t);
        assertEquals(
                Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(imp);
        assertEquals(
                Arrays.asList("import", " ", "a.b.c.D", ";", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void addedImportShouldBePrependedWithEOL() {
        considerCode("import a.A;" + LineSeparator.SYSTEM + "class X{}");

        cu.addImport("a.B");

        assertEqualsStringIgnoringEol("import a.A;\nimport a.B;\nclass X{}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void checkNodeTextCreatedGenericType() {
        String code = "class A {ParseResult<T> result;}";
        considerCode(code);

        FieldDeclaration field =
                cu.getClassByName("A").get().getFieldByName("result").get();
        Node t = field.getCommonType();
        Node t2 = field.getVariable(0).getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(field);
        assertEquals(
                Arrays.asList("ParseResult", "<", "T", ">", " ", "result", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad =
                cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(ad);
        assertEquals(
                Arrays.asList(
                        "public",
                        " ",
                        "@",
                        "interface",
                        " ",
                        "ClassPreamble",
                        " ",
                        "{",
                        " ",
                        "String author();",
                        " ",
                        "}",
                        ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad =
                cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(
                Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad =
                cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(
                Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad =
                cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = ad.getMember(0).asAnnotationMemberDeclaration();
        Type type = md.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(type);
        assertEquals(
                Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = cu.getAnnotationDeclarationByName("ClassPreamble")
                .get()
                .getMember(5)
                .asAnnotationMemberDeclaration();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(
                Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWithoutExpression() {
        considerExpression("new int[]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(
                Arrays.asList("[", "]"),
                nodeText.getElements().stream()
                        .map(TextElement::expand)
                        .filter(e -> !e.isEmpty())
                        .collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWith() {
        considerExpression("new int[123]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(
                Arrays.asList("[", "123", "]"),
                nodeText.getElements().stream()
                        .map(TextElement::expand)
                        .filter(e -> !e.isEmpty())
                        .collect(Collectors.toList()));
    }

    //
    // Tests on findIndentation
    //

    @Test
    void findIndentationForAnnotationMemberDeclarationWithoutComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(4);
        List<TextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(
                Arrays.asList(" ", " ", " "),
                indentation.stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(
                Arrays.asList(" ", " ", " "),
                indentation.stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    //
    // Tests on printing
    //

    @Test
    void printASuperSimpleCUWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASuperSimpleClassWithAFieldAdded() {
        String code = "class A {}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        classA.addField("int", "myField");
        assertEquals(
                "class A {" + LineSeparator.SYSTEM + "    int myField;" + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(classA));
    }

    @Test
    void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
    }

    @Test
    void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t" + LineSeparator.SYSTEM + " int f;" + LineSeparator.SYSTEM
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM + "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
        assertEquals(
                "void foo(int p  ) { return  'z'  \t; }",
                LexicalPreservingPrinter.print(
                        cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t" + LineSeparator.SYSTEM + " int f;"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        // This rendering is probably caused by the concret syntax model
        assertEquals(
                "class /*a comment*/ A {\t\t" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "         void foo(int p  ) { return  'z'  \t; }}",
                LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleClassRemovingAMethod() {
        String code = "class /*a comment*/ A {\t\t" + LineSeparator.SYSTEM + " int f;"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "         void foo(int p  ) { return  'z'  \t; }"
                + LineSeparator.SYSTEM + " int g;}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(1);
        assertEquals(
                "class /*a comment*/ A {\t\t" + LineSeparator.SYSTEM + " int f;" + LineSeparator.SYSTEM
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM + " int g;}",
                LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAStatement() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(
                new BinaryExpr(new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS));
        NodeList<Statement> stmts = cu.getClassByName("A")
                .get()
                .getMethodsByName("foo")
                .get(0)
                .getBody()
                .get()
                .getStatements();
        stmts.add(s);
        MethodDeclaration m =
                cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        assertEquals(
                "void foo(char p1, int p2) {" + LineSeparator.SYSTEM + "    10 + 2;" + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingAStatementCRLF() {
        printASimpleMethodRemovingAStatement("\r\n");
    }

    @Test
    void printASimpleMethodRemovingAStatementLF() {
        printASimpleMethodRemovingAStatement("\n");
    }

    @Test
    void printASimpleMethodRemovingAStatementCR() {
        printASimpleMethodRemovingAStatement("\r");
    }

    private void printASimpleMethodRemovingAStatement(String eol) {
        considerCode("class A {" + eol
                + "\t" + "foo(int a, int b) {" + eol
                + "\t\t" + "int result = a * b;" + eol
                + "\t\t" + "return a * b;" + eol
                + "\t" + "}" + eol
                + "}");

        ExpressionStmt stmt = cu.findAll(ExpressionStmt.class).get(0);
        stmt.remove();

        assertEquals(
                "class A {" + eol
                        + "\t" + "foo(int a, int b) {" + eol
                        + "\t\t" + "return a * b;" + eol
                        + "\t" + "}" + eol
                        + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import a.b.c.D;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void printAnotherImport() {
        String code = "import com.github.javaparser.ast.CompilationUnit;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import com.github.javaparser.ast.CompilationUnit;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void printAStaticImport() {
        String code = "import static com.github.javaparser.ParseStart.*;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        assertEquals("import static com.github.javaparser.ParseStart.*;", LexicalPreservingPrinter.print(imp));
    }

    @Test
    void checkAnnidatedTypeParametersPrinting() {
        String code = "class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }";
        considerCode(code);
        assertEquals(
                "class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASingleCatch() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);

        assertEquals("class A {{try { doit(); } catch (Exception e) {}}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAMultiCatch() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);

        assertEquals(
                "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASingleCatchType() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration =
                (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt =
                (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Type catchType = catchClause.getParameter().getType();

        assertEquals("Exception", LexicalPreservingPrinter.print(catchType));
    }

    @Test
    void printUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration =
                (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt =
                (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        UnionType unionType = (UnionType) catchClause.getParameter().getType();

        assertEquals("Exception | AssertionError", LexicalPreservingPrinter.print(unionType));
    }

    @Test
    void printParameterHavingUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration =
                (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt =
                (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Parameter parameter = catchClause.getParameter();

        assertEquals("Exception | AssertionError e", LexicalPreservingPrinter.print(parameter));
    }

    @Test
    void printLambaWithUntypedParams() {
        String code = "class A {Function<String,String> f = a -> a;}";
        considerCode(code);

        assertEquals("class A {Function<String,String> f = a -> a;}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAModuleInfoSpecificKeywordUsedAsIdentifier1() {
        considerCode("class module { }");

        cu.getClassByName("module").get().setName("xyz");

        assertEquals("class xyz { }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printAModuleInfoSpecificKeywordUsedAsIdentifier2() {
        considerCode("class xyz { }");

        cu.getClassByName("xyz").get().setName("module");

        assertEquals("class module { }", LexicalPreservingPrinter.print(cu));
    }

    // Issue 823: setPackageDeclaration on CU starting with a comment
    @Test
    void reactToSetPackageDeclarationOnCuStartingWithComment() {
        considerCode("// Hey, this is a comment\n" + "\n" + "\n" + "// Another one\n" + "\n" + "class A {}");
        cu.setPackageDeclaration("org.javaparser.lexicalpreservation.examples");
    }

    @Test
    void printLambdaIntersectionTypeAssignment() {
        String code = "class A {" + LineSeparator.SYSTEM + "  void f() {"
                + LineSeparator.SYSTEM + "    Runnable r = (Runnable & Serializable) (() -> {});"
                + LineSeparator.SYSTEM + "    r = (Runnable & Serializable)() -> {};"
                + LineSeparator.SYSTEM + "    r = (Runnable & I)() -> {};"
                + LineSeparator.SYSTEM + "  }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + LineSeparator.SYSTEM
                + "  Object f() {" + LineSeparator.SYSTEM
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); "
                + LineSeparator.SYSTEM
                + "}}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    // See issue #855
    @Test
    void handleOverrideAnnotation() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   @Override"
                + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers().forEach(member -> {
            if (member instanceof MethodDeclaration) {
                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                    methodDeclaration.addAnnotation("Override");
                }
            }
        }));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void preserveSpaceAsIsForASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");
        assertEquals(readExample("ASimpleClassWithMoreFormatting"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void renameASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get().setName("MyRenamedClass");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step1"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void theLexicalPreservationStringForAnAddedMethodShouldBeIndented() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get().setName("MyRenamedClass");
        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get().addMethod("setAField", PUBLIC);
        assertEquals(
                "public void setAField() {" + LineSeparator.SYSTEM + "    }", LexicalPreservingPrinter.print(setter));
    }

    @Test
    void addMethodToASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get().setName("MyRenamedClass");
        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get().addMethod("setAField", PUBLIC);
        TestUtils.assertEqualsStringIgnoringEol(
                readExample("ASimpleClassWithMoreFormatting_step2"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingParameterToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get().setName("MyRenamedClass");
        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get().addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        TestUtils.assertEqualsStringIgnoringEol(
                readExample("ASimpleClassWithMoreFormatting_step3"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void findIndentationOfEmptyMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass")
                .get()
                .getMethodsByName("setAField")
                .get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(
                4,
                LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
    }

    @Test
    void findIndentationOfMethodWithStatements() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass")
                .get()
                .getMethodsByName("setAField")
                .get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(
                4,
                LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
        assertEquals(
                8,
                LexicalPreservingPrinter.findIndentation(setter.getBody().get().getStatement(0))
                        .size());
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get().setName("MyRenamedClass");
        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get().addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        setter.getBody()
                .get()
                .getStatements()
                .add(new ExpressionStmt(new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN)));
        TestUtils.assertEqualsStringIgnoringEol(
                readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormattingFromStep3() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass")
                .get()
                .getMethodsByName("setAField")
                .get(0);
        setter.getBody()
                .get()
                .getStatements()
                .add(new ExpressionStmt(new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN)));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void nodeTextForMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass")
                .get()
                .getMethodsByName("setAField")
                .get(0);
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Modifier.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(VoidType.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(SimpleName.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LPAREN));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Parameter.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RPAREN));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(BlockStmt.class));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get());
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LBRACE));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(ExpressionStmt.class));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RBRACE));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get().getStatement(0));
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(AssignExpr.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SEMICOLON));
        assertEquals(index, nodeText.getElements().size());
    }

    @Test
    void nodeTextForModifiedMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass")
                .get()
                .getMethodsByName("setAField")
                .get(0);
        setter.getBody()
                .get()
                .getStatements()
                .add(new ExpressionStmt(new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN)));
        NodeText nodeText;

        nodeText = getTextForNode(setter);
        int index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Modifier.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(VoidType.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(SimpleName.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LPAREN));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(Parameter.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RPAREN));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(BlockStmt.class));
        assertEquals(index, nodeText.getElements().size());

        nodeText = getTextForNode(setter.getBody().get());
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.LBRACE));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(ExpressionStmt.class));
        assertTrue(nodeText.getElements().get(index++).isNewline());
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SPACE));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.RBRACE));
        assertEquals(index, nodeText.getElements().size());

        nodeText = LexicalPreservingPrinter.getOrCreateNodeText(
                setter.getBody().get().getStatement(0));
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(AssignExpr.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SEMICOLON));
        assertEquals(index, nodeText.getElements().size());
    }

    // See issue #926
    @Test
    void addASecondStatementToExistingMethod() throws IOException {
        considerExample("MethodWithOneStatement");

        MethodDeclaration methodDeclaration =
                cu.getType(0).getMethodsByName("someMethod").get(0);
        methodDeclaration
                .getBody()
                .get()
                .getStatements()
                .add(new ExpressionStmt(new VariableDeclarationExpr(new VariableDeclarator(
                        parseClassOrInterfaceType("String"), "test2", new StringLiteralExpr("")))));
        TestUtils.assertEqualsStringIgnoringEol(
                "public void someMethod() {" + LineSeparator.SYSTEM
                        + "        String test = \"\";" + LineSeparator.SYSTEM
                        + "        String test2 = \"\";" + LineSeparator.SYSTEM
                        // HACK: The right closing brace should not have indentation
                        // because the original method did not introduce indentation,
                        // however due to necessity this test was left with indentation,
                        // in a later version it should be revised.
                        + "    }",
                LexicalPreservingPrinter.print(methodDeclaration));
    }

    // See issue #866
    @Test
    void moveOverrideAnnotations() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected @Override void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers()
                .forEach(member -> member.ifMethodDeclaration(methodDeclaration -> {
                    if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                        while (methodDeclaration.getAnnotations().isNonEmpty()) {
                            AnnotationExpr annotationExpr =
                                    methodDeclaration.getAnnotations().get(0);
                            annotationExpr.remove();
                        }

                        methodDeclaration.addMarkerAnnotation("Override");
                    }
                })));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    // See issue #866
    @Test
    void moveOrAddOverrideAnnotations() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected @Override void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers().forEach(member -> {
            if (member instanceof MethodDeclaration) {
                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                    while (methodDeclaration.getAnnotations().isNonEmpty()) {
                        AnnotationExpr annotationExpr =
                                methodDeclaration.getAnnotations().get(0);
                        annotationExpr.remove();
                    }
                }
                methodDeclaration.addMarkerAnnotation("Override");
            }
        }));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleAddingMarkerAnnotation() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   @Override"
                + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers().forEach(member -> {
            if (member instanceof MethodDeclaration) {
                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                    methodDeclaration.addMarkerAnnotation("Override");
                }
            }
        }));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleOverrideMarkerAnnotation() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers()
                .forEach(member -> member.ifMethodDeclaration(
                        methodDeclaration -> methodDeclaration.addMarkerAnnotation("Override"))));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleOverrideAnnotationAlternative() {
        considerCode("public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void test() {}"
                + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "   protected void initializePage() {}"
                + LineSeparator.SYSTEM + "}");

        cu.getTypes().forEach(type -> type.getMembers()
                .forEach(member ->
                        member.ifMethodDeclaration(methodDeclaration -> methodDeclaration.addAnnotation("Override"))));
        assertEquals(
                "public class TestPage extends Page {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void test() {}"
                        + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                        + "   @Override"
                        + LineSeparator.SYSTEM + "   protected void initializePage() {}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void invokeModifierVisitor() {
        considerCode("class A {" + LineSeparator.SYSTEM
                + "  Object f() {" + LineSeparator.SYSTEM
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); "
                + LineSeparator.SYSTEM
                + "}}");
        cu.accept(new ModifierVisitor<>(), null);
    }

    @Test
    void handleDeprecatedAnnotationFinalClass() {
        considerCode("public final class A {}");

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals(
                "@Deprecated" + LineSeparator.SYSTEM + "public final class A {}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void handleDeprecatedAnnotationAbstractClass() {
        considerCode("public abstract class A {}");

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals(
                "@Deprecated" + LineSeparator.SYSTEM + "public abstract class A {}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void issue1244() {
        considerCode("public class Foo {" + LineSeparator.SYSTEM + LineSeparator.SYSTEM
                + "// Some comment" + LineSeparator.SYSTEM + LineSeparator.SYSTEM // does work with only one \n
                + "public void writeExternal() {}" + LineSeparator.SYSTEM + "}");

        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(c -> {
            List<MethodDeclaration> methods = c.getMethodsByName("writeExternal");
            for (MethodDeclaration method : methods) {
                c.remove(method);
            }
        });
        assertEqualsStringIgnoringEol(
                "public class Foo {\n" + "// Some comment\n\n" + "}", LexicalPreservingPrinter.print(cu));
    }

    static class AddFooCallModifierVisitor extends ModifierVisitor<Void> {
        @Override
        public Visitable visit(MethodCallExpr n, Void arg) {
            // Add a call to foo() on every found method call
            return new MethodCallExpr(n, "foo");
        }
    }

    // See issue 1277
    @Test
    void testInvokeModifierVisitor() {
        considerCode("class A {" + LineSeparator.SYSTEM + "  public String message = \"hello\";"
                + LineSeparator.SYSTEM + "   void bar() {"
                + LineSeparator.SYSTEM + "     System.out.println(\"hello\");"
                + LineSeparator.SYSTEM + "   }"
                + LineSeparator.SYSTEM + "}");

        cu.accept(new AddFooCallModifierVisitor(), null);
    }

    static class CallModifierVisitor extends ModifierVisitor<Void> {
        @Override
        public Visitable visit(MethodCallExpr n, Void arg) {
            // Add a call to foo() on every found method call
            return new MethodCallExpr(n.clone(), "foo");
        }
    }

    @Test
    void invokeModifierVisitorIssue1297() {
        considerCode("class A {" + LineSeparator.SYSTEM + "   public void bar() {"
                + LineSeparator.SYSTEM + "     System.out.println(\"hello\");"
                + LineSeparator.SYSTEM + "     System.out.println(\"hello\");"
                + LineSeparator.SYSTEM + "     // comment"
                + LineSeparator.SYSTEM + "   }"
                + LineSeparator.SYSTEM + "}");

        cu.accept(new CallModifierVisitor(), null);
    }

    @Test
    void addedBlockCommentsPrinted() {
        considerCode("public class Foo { }");

        cu.getClassByName("Foo").get().addMethod("mymethod").setBlockComment("block");
        assertEqualsStringIgnoringEol(
                "public class Foo {" + LineSeparator.SYSTEM + "    /*block*/"
                        + LineSeparator.SYSTEM + "    void mymethod() {"
                        + LineSeparator.SYSTEM + "    }"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addedLineCommentsPrinted() {
        considerCode("public class Foo { }");

        cu.getClassByName("Foo").get().addMethod("mymethod").setLineComment("line");
        assertEqualsStringIgnoringEol(
                "public class Foo {" + LineSeparator.SYSTEM + "    //line"
                        + LineSeparator.SYSTEM + "    void mymethod() {"
                        + LineSeparator.SYSTEM + "    }"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removedLineCommentsPrinted() {
        considerCode("public class Foo {" + LineSeparator.SYSTEM + "//line"
                + LineSeparator.SYSTEM + "void mymethod() {"
                + LineSeparator.SYSTEM + "}"
                + LineSeparator.SYSTEM + "}");
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol(
                "public class Foo {" + LineSeparator.SYSTEM + "void mymethod() {"
                        + LineSeparator.SYSTEM + "}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    // Checks if comments get removed properly with Unix style line endings
    @Test
    void removedLineCommentsPrintedUnix() {
        considerCode("public class Foo {" + "\n" + "//line" + "\n" + "void mymethod() {" + "\n" + "}" + "\n" + "}");
        cu.getAllContainedComments().get(0).remove();

        assertEquals(
                "public class Foo {" + "\n" + "void mymethod() {" + "\n" + "}" + "\n" + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removedBlockCommentsPrinted() {
        considerCode("public class Foo {" + LineSeparator.SYSTEM + "/*"
                + LineSeparator.SYSTEM + "Block comment coming through"
                + LineSeparator.SYSTEM + "*/"
                + LineSeparator.SYSTEM + "void mymethod() {"
                + LineSeparator.SYSTEM + "}"
                + LineSeparator.SYSTEM + "}");
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol(
                "public class Foo {" + LineSeparator.SYSTEM + "void mymethod() {"
                        + LineSeparator.SYSTEM + "}"
                        + LineSeparator.SYSTEM + "}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void testFixIndentOfMovedNode() {
        try {
            considerExample("FixIndentOfMovedNode");

            cu.getClassByName("ThisIsASampleClass")
                    .get()
                    .getMethodsByName("longerMethod")
                    .get(0)
                    .setBlockComment("Lorem ipsum dolor sit amet, consetetur sadipscing elitr.");

            cu.getClassByName("Foo")
                    .get()
                    .getFieldByName("myFoo")
                    .get()
                    .setLineComment("sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat");

            String expectedCode = readExample("FixIndentOfMovedNodeExpected");
            assertEquals(expectedCode, LexicalPreservingPrinter.print(cu));
        } catch (IOException ex) {
            fail("Could not read test code", ex);
        }
    }

    @Test
    void issue1321() {
        considerCode("class X { X() {} private void testme() {} }");

        ClassOrInterfaceDeclaration type = cu.getClassByName("X").get();
        type.getConstructors().get(0).setBody(new BlockStmt().addStatement("testme();"));

        assertEqualsStringIgnoringEol(
                "class X { X() {\n    testme();\n} private void testme() {} }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void issue2001() {
        considerCode("class X {void blubb(){X.p(\"blaubb04\");}}");

        cu.findAll(MethodCallExpr.class).forEach(Node::removeForced);

        assertEqualsStringIgnoringEol("class X {void blubb(){}}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void testIndentOfCodeBlocks() throws IOException {
        considerExample("IndentOfInsertedCodeBlocks");

        IfStmt ifStmt = new IfStmt();
        ifStmt.setCondition(StaticJavaParser.parseExpression("name.equals(\"foo\")"));
        BlockStmt blockStmt = new BlockStmt();
        blockStmt.addStatement(StaticJavaParser.parseStatement("int i = 0;"));
        blockStmt.addStatement(StaticJavaParser.parseStatement("System.out.println(i);"));
        blockStmt.addStatement(new IfStmt()
                .setCondition(StaticJavaParser.parseExpression("i < 0"))
                .setThenStmt(new BlockStmt().addStatement(StaticJavaParser.parseStatement("i = 0;"))));
        blockStmt.addStatement(StaticJavaParser.parseStatement("new Object(){};"));
        ifStmt.setThenStmt(blockStmt);
        ifStmt.setElseStmt(new BlockStmt());

        cu.findFirst(BlockStmt.class).get().addStatement(ifStmt);
        String expected = considerExample("IndentOfInsertedCodeBlocksExpected");
        TestUtils.assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void commentAddedAtTopLevel() {
        considerCode("package x;class X{}");

        cu.setComment(new LineComment("Bla"));
        assertEqualsStringIgnoringEol("//Bla\npackage x;class X{}", LexicalPreservingPrinter.print(cu));

        cu.setComment(new LineComment("BlaBla"));
        assertEqualsStringIgnoringEol("//BlaBla\npackage x;class X{}", LexicalPreservingPrinter.print(cu));

        cu.removeComment();
        assertEqualsStringIgnoringEol("package x;class X{}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void testReplaceStringLiteral() {
        considerExpression("\"asd\"");
        final String expected = "\"REPLACEMENT\"";

        assertTrue(expression.isStringLiteralExpr());
        StringLiteralExpr sle = (StringLiteralExpr) expression;
        sle.setValue("REPLACEMENT");

        final String actual = LexicalPreservingPrinter.print(expression);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceStringLiteralWithinStatement() {
        considerStatement("String str = \"aaa\";");
        String expected = "String str = \"REPLACEMENT\";";

        statement.findAll(StringLiteralExpr.class).forEach(stringLiteralExpr -> {
            stringLiteralExpr.setValue("REPLACEMENT");
        });

        assertEquals(expected, LexicalPreservingPrinter.print(statement));
        assertEquals(expected, statement.toString());
    }

    @Test
    public void testReplaceClassName() {
        considerCode("class A {}");

        assertEquals(1, cu.findAll(ClassOrInterfaceDeclaration.class).size());
        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(coid -> coid.setName("B"));

        final String expected = "class B {}";

        final String actual = LexicalPreservingPrinter.print(cu);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceIntLiteral() {
        considerExpression("5");
        final String expected = "10";

        assertTrue(expression.isIntegerLiteralExpr());
        ((IntegerLiteralExpr) expression).setValue("10");

        final String actual = LexicalPreservingPrinter.print(expression);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceLongLiteral() {
        considerStatement("long x = 5L;");
        String expected = "long x = 10L;";

        statement.findAll(LongLiteralExpr.class).forEach(longLiteralExpr -> {
            longLiteralExpr.setValue("10L");
        });

        final String actual = LexicalPreservingPrinter.print(statement);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceBooleanLiteral() {
        considerStatement("boolean x = true;");
        String expected = "boolean x = false;";

        statement.findAll(BooleanLiteralExpr.class).forEach(booleanLiteralExpr -> {
            booleanLiteralExpr.setValue(false);
        });

        final String actual = LexicalPreservingPrinter.print(statement);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceDoubleLiteral() {
        considerStatement("double x = 5.0D;");
        String expected = "double x = 10.0D;";

        statement.findAll(DoubleLiteralExpr.class).forEach(doubleLiteralExpr -> {
            doubleLiteralExpr.setValue("10.0D");
        });

        final String actual = LexicalPreservingPrinter.print(statement);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceCharLiteral() {
        considerStatement("char x = 'a';");
        String expected = "char x = 'b';";

        statement.findAll(CharLiteralExpr.class).forEach(charLiteralExpr -> {
            charLiteralExpr.setValue("b");
        });

        final String actual = LexicalPreservingPrinter.print(statement);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceCharLiteralUnicode() {
        considerStatement("char x = 'a';");
        String expected = "char x = '\\u0000';";

        statement.findAll(CharLiteralExpr.class).forEach(charLiteralExpr -> {
            charLiteralExpr.setValue("\\u0000");
        });

        final String actual = LexicalPreservingPrinter.print(statement);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceTextBlockLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLexicalPreservationEnabled(true)
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_14));

        String code = "String x = \"\"\"a\"\"\";";
        String expected = "String x = \"\"\"\n" + "     REPLACEMENT\n" + "     \"\"\";";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(TextBlockLiteralExpr.class).forEach(textblockLiteralExpr -> {
            textblockLiteralExpr.setValue("\n     REPLACEMENT\n     ");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    void testTextBlockSupport() {
        String code = "String html = \"\"\"\n" + "  <html>\n"
                + "    <body>\n"
                + "      <p>Hello, world</p>\n"
                + "    </body>\n"
                + "  </html>\n"
                + "\"\"\";";
        String expected = "String html = \"\"\"\r\n"
                + "  <html>\r\n"
                + "    <body>\r\n"
                + "      <p>Hello, world</p>\r\n"
                + "    </body>\r\n"
                + "  </html>\r\n"
                + "\"\"\";";
        final JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setLexicalPreservationEnabled(true)
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_15));
        Statement stmt = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        LexicalPreservingPrinter.setup(stmt);
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(stmt));
    }

    @Test
    void testArrayPreservation_WithSingleLanguageStyle() {

        // Given
        considerCode("class Test {\n" + "  int[] foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int[] foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testArrayPreservation_WithMultipleLanguageStyle() {

        // Given
        considerCode("class Test {\n" + "  int[][] foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int[][] foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testArrayPreservation_WithSingleCLanguageStyle() {

        // Given
        considerCode("class Test {\n" + "  int foo[];\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int foo[];\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    /**
     * Given a field that have arrays declared in C style and
     * When a marker annotation is added to the code
     * Assert that the result matches the expected.
     *
     * Issue: 3419
     */
    @Test
    void testArrayPreservation_WithMultipleCLanguageStyle() {

        // Given
        considerCode("class Test {\n" + "  int foo[][];\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int foo[][];\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testArrayPreservation_WithSingleBracketWithoutSpace() {

        // Given
        considerCode("class Test {\n" + "  int[]foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int[]foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testArrayPreservation_WithMultipleBracketWithoutSpace() {

        // Given
        considerCode("class Test {\n" + "  int[][]foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  int[][]foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testClassOrInterfacePreservationWithFullyQualifiedName_SingleType() {
        // Given
        considerCode("class Test {\n" + "  java.lang.Object foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        // modification of the AST
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  java.lang.Object foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testClassOrInterfacePreservationWithFullyQualifiedName_ArrayType() {
        // Given
        considerCode("class Test {\n" + "  java.lang.Object[] foo;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        // modification of the AST
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  java.lang.Object[] foo;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testClassOrInterfacePreservationWithFullyQualifiedName_MultipleVariablesDeclarationWithSameType() {
        // Given
        considerCode("class Test {\n" + "  java.lang.Object[] foo, bar;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        // modification of the AST
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  java.lang.Object[] foo, bar;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    @Test
    void testClassOrInterfacePreservationWithFullyQualifiedName_MultipleVariablesDeclarationwithDifferentType() {
        // Given
        considerCode("class Test {\n" + "  java.lang.Object foo[], bar;\n" + "}");

        // When
        FieldDeclaration fooField = cu.findFirst(FieldDeclaration.class).orElseThrow(AssertionError::new);
        // modification of the AST
        fooField.addMarkerAnnotation("Nullable");

        // Assert
        String expectedCode = "class Test {\n" + "  @Nullable\n" + "  java.lang.Object foo[], bar;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    // issue 3588 Modifier is removed when removing an annotation.
    @Test
    void testRemovingInlinedAnnotation() {
        // Given
        considerCode("public class Foo{\n" + "     protected @Nullable Object bar;\n" + "}");

        // When
        FieldDeclaration fd = cu.findFirst(FieldDeclaration.class).get();
        // modification of the AST
        AnnotationExpr ae = fd.getAnnotations().get(0);
        ae.remove();

        // Assert
        String expectedCode = "public class Foo{\n" + "     protected Object bar;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    // issue 3588 Modifier is removed when removing an annotation.
    @Test
    void testRemovingInlinedAnnotation_alternate_case() {
        // Given
        considerCode("public class Foo{\n" + "     @Nullable protected Object bar;\n" + "}");

        // When
        FieldDeclaration fd = cu.findFirst(FieldDeclaration.class).get();
        // modification of the AST
        AnnotationExpr ae = fd.getAnnotations().get(0);
        ae.remove();

        // Assert
        String expectedCode = "public class Foo{\n" + "     protected Object bar;\n" + "}";
        assertTransformedToString(expectedCode, cu);
    }

    // issue 3216 LexicalPreservingPrinter add Wrong indentation when removing comments
    @Test
    void removedIndentationLineCommentsPrinted() {
        considerCode("public class Foo {\n" + "  //line \n" + "  void mymethod() {\n" + "  }\n" + "}");
        String expected = "public class Foo {\n" + "  void mymethod() {\n" + "  }\n" + "}";
        cu.getAllContainedComments().get(0).remove();
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    // issue 4311  IllegalStateException when removing all comments with LexicalPreservingPrinter
    @Test
    void removedLineCommentsWithSameContent() {
        considerCode(
                "public class Foo {\n" + "  //line 1 \n" + "  //line 1 \n" + "  void mymethod() {\n" + "  }\n" + "}");
        String expected = "public class Foo {\n" + "  void mymethod() {\n" + "  }\n" + "}";
        cu.getAllContainedComments().stream().forEach(c -> c.remove());
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    // issue 3216 LexicalPreservingPrinter add Wrong indentation when removing comments
    @Test
    void removedIndentationBlockCommentsPrinted() {
        considerCode("public class Foo {\n" + "  /*\n"
                + "  *Block comment coming through\n"
                + "  */\n"
                + "  void mymethod() {\n"
                + "  }\n"
                + "}");
        String expected = "public class Foo {\n" + "  void mymethod() {\n" + "  }\n" + "}";
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    // issue 3216 LexicalPreservingPrinter add Wrong indentation when removing comments
    @Test
    void removedIndentationJavaDocCommentsPrinted() {
        considerCode("public class Foo {\n" + "  /**\n"
                + "   *JavaDoc comment coming through\n"
                + "   */\n"
                + "  void mymethod() {\n"
                + "  }\n"
                + "}");
        String expected = "public class Foo {\n" + "  void mymethod() {\n" + "  }\n" + "}";
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingOrphanCommentToType() {
        String actual = "public class Foo {\n" + "}";

        String expected = "//added comment\n" + "public class Foo {\n" + "}";

        considerCode(actual);
        cu.getTypes().get(0).addOrphanComment(new LineComment("added comment"));
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingOrphanCommentToBlock() {
        String actual = "public class Foo {\n" + "}";

        String expected = "//added comment\n" + "public class Foo {\n" + "}";

        considerCode(actual);
        cu.getTypes().get(0).getChildNodes().get(0).addOrphanComment(new LineComment("added comment"));
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingOrphanCommentToBlockInMethodDeclaration() {
        String actual = "public class Foo {\n" + "  boolean m() {\n" + "    return true;\n" + "  }\n" + "}";

        // that's probably not what we want,
        // but this is what is implemented in LexicalPreservingPrinter.Observer.concretePropertyChange(..)
        String expected = "public class Foo {\n"
                + "  boolean m() //added comment\n"
                + "{\n"
                + "    return true;\n"
                + "  }\n"
                + "}";

        considerCode(actual);
        cu.findAll(BlockStmt.class).get(0).addOrphanComment(new LineComment("added comment"));
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingOrphanCommentToBlockInMethodDeclaration2() {
        String actual = "public class Foo {\n" + "  boolean m() \n" + "  {\n" + "    return true;\n" + "  }\n" + "}";

        String expected = "public class Foo {\n"
                + "  boolean m() \n"
                + "  //added comment\n"
                + "  {\n"
                + "    return true;\n"
                + "  }\n"
                + "}";

        considerCode(actual);
        cu.findAll(BlockStmt.class).get(0).addOrphanComment(new LineComment("added comment"));
        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

    // issue 3800 determine whether active
    @Test
    void checkLPPIsAvailableOnNode() {
        String code = "class A {void foo(int p1, float p2) { }}";
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodDeclaration md = cu.findFirst(MethodDeclaration.class).get();
        LexicalPreservingPrinter.setup(md);

        assertTrue(LexicalPreservingPrinter.isAvailableOn(md));
        assertFalse(LexicalPreservingPrinter.isAvailableOn(cu));
    }

    // issue 4442
    @Test
    void handleUnexpectedToken() {
        String code = "public class Foo {\n" + ";\n"
                + // <-- this is the unexpected token
                "    public void func(){};\n"
                + "\n"
                + "}";

        String expected = "import com.github.javaparser.ast.Generated;\n"
                + "\n"
                + "@Generated\n"
                + "public class Foo {\n"
                + ";\n"
                + "    public void func(){};\n"
                + "\n"
                + "}";

        considerCode(code);

        ClassOrInterfaceDeclaration md =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();
        md.addAnnotation(Generated.class);
        String modifiedContent = LexicalPreservingPrinter.print(cu);
        System.out.println(modifiedContent);
        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    // issue 1821 Switch toString to LexicalPreservingPrinter when configured
    @Test
    void checkLPPIsDefaultPrinter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        StaticJavaParser.getParserConfiguration().setLexicalPreservationEnabled(true);
        CompilationUnit cu = StaticJavaParser.parse(code);
        assertEquals(code, cu.toString());
    }

    @Test
    void checkLegacyLPPExecution() {
        String code = "class A {void foo(int p1, float p2) { }}";
        StaticJavaParser.getParserConfiguration().setLexicalPreservationEnabled(true);
        CompilationUnit cu = StaticJavaParser.parse(code);
        LexicalPreservingPrinter.setup(cu);
        assertEquals(cu.toString(), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void checkLPPIsNotDefaultPrinter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        CompilationUnit cu = StaticJavaParser.parse(code);
        assertNotEquals(code, cu.toString());
    }
}
