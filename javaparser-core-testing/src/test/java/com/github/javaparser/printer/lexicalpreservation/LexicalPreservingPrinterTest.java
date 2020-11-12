/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseClassOrInterfaceType;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter.NODE_TEXT_DATA;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

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
        assertEquals(cu.getClassByName("A").get(),
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
        assertEquals(GeneratedJavaParserConstants.EOF,
                ((TokenTextElement) getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(fd);
        assertEquals(Arrays.asList("int", " ", "i", ";"),
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
        assertEquals(Arrays.asList("i"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
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
        assertEquals(Arrays.asList("int", " ", "p1"),
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
        assertEquals(Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration) cu.getChildNodes().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(imp);
        assertEquals(Arrays.asList("import", " ", "a.b.c.D", ";", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void addedImportShouldBePrependedWithEOL() {
        considerCode("import a.A;" + SYSTEM_EOL + "class X{}");

        cu.addImport("a.B");

        assertEqualsStringIgnoringEol("import a.A;\nimport a.B;\nclass X{}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void checkNodeTextCreatedGenericType() {
        String code = "class A {ParseResult<T> result;}";
        considerCode(code);

        FieldDeclaration field = cu.getClassByName("A").get().getFieldByName("result").get();
        Node t = field.getCommonType();
        Node t2 = field.getVariable(0).getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(field);
        assertEquals(Arrays.asList("ParseResult", "<", "T", ">", " ", "result", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(ad);
        assertEquals(
                Arrays.asList("public", " ", "@", "interface", " ", "ClassPreamble", " ", "{", " ", "String author();",
                        " ", "}", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration) ad.getMember(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = ad.getMember(0).asAnnotationMemberDeclaration();
        Type type = md.getType();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(type);
        assertEquals(Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5)
                .asAnnotationMemberDeclaration();
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWithoutExpression() {
        considerExpression("new int[]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty())
                        .collect(Collectors.toList()));
    }

    @Test
    void checkNodeTextCreatedArrayCreationLevelWith() {
        considerExpression("new int[123]");

        ArrayCreationExpr arrayCreationExpr = expression.asArrayCreationExpr();
        ArrayCreationLevel arrayCreationLevel = arrayCreationExpr.getLevels().get(0);
        NodeText nodeText = LexicalPreservingPrinter.getOrCreateNodeText(arrayCreationLevel);
        assertEquals(Arrays.asList("[", "123", "]"),
                nodeText.getElements().stream().map(TextElement::expand).filter(e -> !e.isEmpty())
                        .collect(Collectors.toList()));
    }

    //
    // Tests on findIndentation
    //

    @Test
    void findIndentationForAnnotationMemberDeclarationWithoutComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(4);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "),
                indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
    }

    @Test
    void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TokenTextElement> indentation = LexicalPreservingPrinter.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "),
                indentation.stream().map(TokenTextElement::expand).collect(Collectors.toList()));
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
        assertEquals("class A {" + SYSTEM_EOL + "    int myField;" + SYSTEM_EOL + "}", LexicalPreservingPrinter.print(classA));
    }

    @Test
    void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
    }

    @Test
    void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t" + SYSTEM_EOL + " int f;" + SYSTEM_EOL + SYSTEM_EOL + SYSTEM_EOL
                + "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
        assertEquals(code, LexicalPreservingPrinter.print(cu.getClassByName("A").get()));
        assertEquals("void foo(int p  ) { return  'z'  \t; }",
                LexicalPreservingPrinter.print(cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t" + SYSTEM_EOL +
                " int f;" + SYSTEM_EOL + SYSTEM_EOL + SYSTEM_EOL +
                "         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t" + SYSTEM_EOL +
                SYSTEM_EOL +
                "         void foo(int p  ) { return  'z'  \t; }}", LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleClassRemovingAMethod() {
        String code = "class /*a comment*/ A {\t\t" + SYSTEM_EOL +
                " int f;" + SYSTEM_EOL + SYSTEM_EOL + SYSTEM_EOL +
                "         void foo(int p  ) { return  'z'  \t; }" + SYSTEM_EOL +
                " int g;}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(1);
        assertEquals("class /*a comment*/ A {\t\t" + SYSTEM_EOL +
                " int f;" + SYSTEM_EOL + SYSTEM_EOL + SYSTEM_EOL +
                " int g;}", LexicalPreservingPrinter.print(c));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", LexicalPreservingPrinter.print(m));
    }

    @Test
    void printASimpleMethodAddingAStatement() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS));
        NodeList<Statement> stmts = cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get()
                .getStatements();
        stmts.add(s);
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        assertEquals("void foo(char p1, int p2) {" + SYSTEM_EOL +
                "    10 + 2;" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(m));
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
        String code = "class A {" + eol
                + "\t" + "foo(int a, int b) {" + eol
                + "\t\t" + "int result = a * b;" + eol
                + "\t\t" + "return a * b;" + eol
                + "\t" + "}" + eol
                + "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        ExpressionStmt stmt = cu.findAll(ExpressionStmt.class).get(0);
        stmt.remove();

        assertEquals("class A {" + eol
                + "\t" + "foo(int a, int b) {" + eol
                + "\t\t" + "return a * b;" + eol
                + "\t" + "}" + eol
                + "}", LexicalPreservingPrinter.print(cu));
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
        assertEquals("class A { private final Stack<Iterator<Triple>> its = new Stack<Iterator<Triple>>(); }",
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

        assertEquals("class A {{try { doit(); } catch (Exception | AssertionError e) {}}}",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printASingleCatchType() {
        String code = "class A {{try { doit(); } catch (Exception e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        Type catchType = catchClause.getParameter().getType();

        assertEquals("Exception", LexicalPreservingPrinter.print(catchType));
    }

    @Test
    void printUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
        CatchClause catchClause = tryStmt.getCatchClauses().get(0);
        UnionType unionType = (UnionType) catchClause.getParameter().getType();

        assertEquals("Exception | AssertionError", LexicalPreservingPrinter.print(unionType));
    }

    @Test
    void printParameterHavingUnionType() {
        String code = "class A {{try { doit(); } catch (Exception | AssertionError e) {}}}";
        considerCode(code);
        InitializerDeclaration initializerDeclaration = (InitializerDeclaration) cu.getType(0).getMembers().get(0);
        TryStmt tryStmt = (TryStmt) initializerDeclaration.getBody().getStatements().get(0);
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
        considerCode("// Hey, this is a comment\n" +
                "\n" +
                "\n" +
                "// Another one\n" +
                "\n" +
                "class A {}");
        cu.setPackageDeclaration("org.javaparser.lexicalpreservation.examples");
    }

    @Test
    void printLambdaIntersectionTypeAssignment() {
        String code = "class A {" + SYSTEM_EOL +
                "  void f() {" + SYSTEM_EOL +
                "    Runnable r = (Runnable & Serializable) (() -> {});" + SYSTEM_EOL +
                "    r = (Runnable & Serializable)() -> {};" + SYSTEM_EOL +
                "    r = (Runnable & I)() -> {};" + SYSTEM_EOL +
                "  }}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    @Test
    void printLambdaIntersectionTypeReturn() {
        String code = "class A {" + SYSTEM_EOL
                + "  Object f() {" + SYSTEM_EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); "
                + SYSTEM_EOL
                + "}}";
        considerCode(code);

        assertEquals(code, LexicalPreservingPrinter.print(cu));
    }

    // See issue #855
    @Test
    void handleOverrideAnnotation() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> {
                            if (member instanceof MethodDeclaration) {
                                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                                    methodDeclaration.addAnnotation("Override");
                                }
                            }
                        }));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override()" + SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void preserveSpaceAsIsForASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");
        assertEquals(readExample("ASimpleClassWithMoreFormatting"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void renameASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step1"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void theLexicalPreservationStringForAnAddedMethodShouldBeIndented() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        assertEquals("public void setAField() {" + SYSTEM_EOL +
                "    }", LexicalPreservingPrinter.print(setter));
    }

    @Test
    void addMethodToASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        TestUtils.assertEqualsStringIgnoringEol(readExample("ASimpleClassWithMoreFormatting_step2"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingParameterToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        TestUtils.assertEqualsStringIgnoringEol(readExample("ASimpleClassWithMoreFormatting_step3"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void findIndentationOfEmptyMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
    }

    @Test
    void findIndentationOfMethodWithStatements() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter).size());
        assertEquals(4, LexicalPreservingPrinter.findIndentation(setter.getBody().get()).size());
        assertEquals(8, LexicalPreservingPrinter.findIndentation(setter.getBody().get().getStatement(0)).size());
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormatting() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting");

        cu.getClassByName("ASimpleClass").get()
                .setName("MyRenamedClass");
        MethodDeclaration setter = cu
                .getClassByName("MyRenamedClass").get()
                .addMethod("setAField", PUBLIC);
        setter.addParameter("boolean", "aField");
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN)));
        TestUtils.assertEqualsStringIgnoringEol(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addingStatementToAnAddedMethodInASimpleClassWithMoreFormattingFromStep3() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step3");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
                        new FieldAccessExpr(new ThisExpr(), "aField"),
                        new NameExpr("aField"),
                        AssignExpr.Operator.ASSIGN)));
        assertEquals(readExample("ASimpleClassWithMoreFormatting_step4"), LexicalPreservingPrinter.print(cu));
    }

    @Test
    void nodeTextForMethod() throws IOException {
        considerExample("ASimpleClassWithMoreFormatting_step4");

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
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

        MethodDeclaration setter = cu.getClassByName("MyRenamedClass").get()
                .getMethodsByName("setAField").get(0);
        setter.getBody().get().getStatements().add(new ExpressionStmt(
                new AssignExpr(
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

        nodeText = LexicalPreservingPrinter.getOrCreateNodeText(setter.getBody().get().getStatement(0));
        index = 0;
        assertTrue(nodeText.getElements().get(index++).isChildOfClass(AssignExpr.class));
        assertTrue(nodeText.getElements().get(index++).isToken(GeneratedJavaParserConstants.SEMICOLON));
        assertEquals(index, nodeText.getElements().size());
    }

    // See issue #926
    @Test
    void addASecondStatementToExistingMethod() throws IOException {
        considerExample("MethodWithOneStatement");

        MethodDeclaration methodDeclaration = cu.getType(0).getMethodsByName("someMethod").get(0);
        methodDeclaration.getBody().get().getStatements().add(new ExpressionStmt(
                new VariableDeclarationExpr(
                        new VariableDeclarator(
                                parseClassOrInterfaceType("String"),
                                "test2",
                                new StringLiteralExpr("")))));
        TestUtils.assertEqualsStringIgnoringEol("public void someMethod() {" + SYSTEM_EOL
                + "        String test = \"\";" + SYSTEM_EOL
                + "        String test2 = \"\";" + SYSTEM_EOL
                // HACK: The right closing brace should not have indentation
                // because the original method did not introduce indentation,
                // however due to necessity this test was left with indentation,
                // in a later version it should be revised.
                + "    }", LexicalPreservingPrinter.print(methodDeclaration));
    }

    // See issue #866
    @Test
    void moveOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected @Override void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> member.ifMethodDeclaration(methodDeclaration -> {
                            if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                                while (methodDeclaration.getAnnotations().isNonEmpty()) {
                                    AnnotationExpr annotationExpr = methodDeclaration.getAnnotations().get(0);
                                    annotationExpr.remove();
                                }

                                methodDeclaration.addMarkerAnnotation("Override");
                            }
                        })));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #866
    @Test
    void moveOrAddOverrideAnnotations() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected @Override void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> {
                            if (member instanceof MethodDeclaration) {
                                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                if (methodDeclaration.getAnnotationByName("Override").isPresent()) {

                                    while (methodDeclaration.getAnnotations().isNonEmpty()) {
                                        AnnotationExpr annotationExpr = methodDeclaration.getAnnotations().get(0);
                                        annotationExpr.remove();
                                    }
                                }
                                methodDeclaration.addMarkerAnnotation("Override");
                            }
                        }));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleAddingMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> {
                            if (member instanceof MethodDeclaration) {
                                MethodDeclaration methodDeclaration = (MethodDeclaration) member;
                                if (!methodDeclaration.getAnnotationByName("Override").isPresent()) {
                                    methodDeclaration.addMarkerAnnotation("Override");
                                }
                            }
                        }));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleOverrideMarkerAnnotation() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> member.ifMethodDeclaration(
                                methodDeclaration -> methodDeclaration.addMarkerAnnotation("Override"))));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // See issue #865
    @Test
    void handleOverrideAnnotationAlternative() {
        String code = "public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes()
                .forEach(type -> type.getMembers()
                        .forEach(member -> member.ifMethodDeclaration(
                                methodDeclaration -> methodDeclaration.addAnnotation("Override"))));
        assertEquals("public class TestPage extends Page {" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override()" + SYSTEM_EOL +
                "   protected void test() {}" + SYSTEM_EOL +
                SYSTEM_EOL +
                "   @Override()" + SYSTEM_EOL +
                "   protected void initializePage() {}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void invokeModifierVisitor() {
        String code = "class A {" + SYSTEM_EOL
                + "  Object f() {" + SYSTEM_EOL
                + "    return (Comparator<Map.Entry<K, V>> & Serializable)(c1, c2) -> c1.getKey().compareTo(c2.getKey()); "
                + SYSTEM_EOL
                + "}}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new ModifierVisitor<>(), null);
    }

    @Test
    void handleDeprecatedAnnotationFinalClass() {
        String code = "public final class A {}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + SYSTEM_EOL +
                "public final class A {}", LexicalPreservingPrinter.print(cu));

    }

    @Test
    void handleDeprecatedAnnotationAbstractClass() {
        String code = "public abstract class A {}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getTypes().forEach(type -> type.addAndGetAnnotation(Deprecated.class));

        assertEquals("@Deprecated()" + SYSTEM_EOL +
                "public abstract class A {}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void issue1244() {
        String code = "public class Foo {" + SYSTEM_EOL + SYSTEM_EOL
                + "// Some comment" + SYSTEM_EOL + SYSTEM_EOL // does work with only one \n
                + "public void writeExternal() {}" + SYSTEM_EOL + "}";
        CompilationUnit originalCu = parse(code);
        CompilationUnit cu = LexicalPreservingPrinter.setup(originalCu);

        cu.findAll(ClassOrInterfaceDeclaration.class).forEach(c -> {
            List<MethodDeclaration> methods = c.getMethodsByName("writeExternal");
            for (MethodDeclaration method : methods) {
                c.remove(method);
            }
        });
        assertEqualsStringIgnoringEol("public class Foo {\n" +
                "// Some comment\n\n" +
                "}", LexicalPreservingPrinter.print(cu));
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
        String code = "class A {" + SYSTEM_EOL +
                "  public String message = \"hello\";" + SYSTEM_EOL +
                "   void bar() {" + SYSTEM_EOL +
                "     System.out.println(\"hello\");" + SYSTEM_EOL +
                "   }" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
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
        String code = "class A {" + SYSTEM_EOL +
                "   public void bar() {" + SYSTEM_EOL +
                "     System.out.println(\"hello\");" + SYSTEM_EOL +
                "     System.out.println(\"hello\");" + SYSTEM_EOL +
                "     // comment" + SYSTEM_EOL +
                "   }" + SYSTEM_EOL +
                "}";

        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.accept(new CallModifierVisitor(), null);
    }

    @Test
    void addedBlockCommentsPrinted() {
        String code = "public class Foo { }";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getClassByName("Foo").get()
                .addMethod("mymethod")
                .setBlockComment("block");
        assertEqualsStringIgnoringEol("public class Foo {" + SYSTEM_EOL +
                "    /*block*/" + SYSTEM_EOL +
                "    void mymethod() {" + SYSTEM_EOL +
                "    }" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void addedLineCommentsPrinted() {
        String code = "public class Foo { }";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);

        cu.getClassByName("Foo").get()
                .addMethod("mymethod")
                .setLineComment("line");
        assertEqualsStringIgnoringEol("public class Foo {" + SYSTEM_EOL +
                "    //line" + SYSTEM_EOL +
                "    void mymethod() {" + SYSTEM_EOL +
                "    }" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removedLineCommentsPrinted() {
        String code = "public class Foo {" + SYSTEM_EOL +
                "//line" + SYSTEM_EOL +
                "void mymethod() {" + SYSTEM_EOL +
                "}" + SYSTEM_EOL +
                "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol("public class Foo {" + SYSTEM_EOL +
                "void mymethod() {" + SYSTEM_EOL +
                "}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    // Checks if comments get removed properly with Unix style line endings
    @Test
    void removedLineCommentsPrintedUnix() {
        String code = "public class Foo {" + "\n" +
                "//line" + "\n" +
                "void mymethod() {" + "\n" +
                "}" + "\n" +
                "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();

        assertEquals("public class Foo {" + "\n" +
                "void mymethod() {" + "\n" +
                "}" + "\n" +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removedBlockCommentsPrinted() {
        String code = "public class Foo {" + SYSTEM_EOL +
                "/*" + SYSTEM_EOL +
                "Block comment coming through" + SYSTEM_EOL +
                "*/" + SYSTEM_EOL +
                "void mymethod() {" + SYSTEM_EOL +
                "}" + SYSTEM_EOL +
                "}";
        CompilationUnit cu = parse(code);
        LexicalPreservingPrinter.setup(cu);
        cu.getAllContainedComments().get(0).remove();

        assertEqualsStringIgnoringEol("public class Foo {" + SYSTEM_EOL +
                "void mymethod() {" + SYSTEM_EOL +
                "}" + SYSTEM_EOL +
                "}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void testFixIndentOfMovedNode() {
        try {
            CompilationUnit compilationUnit = parse(readExample("FixIndentOfMovedNode"));
            LexicalPreservingPrinter.setup(compilationUnit);

            compilationUnit.getClassByName("ThisIsASampleClass").get()
                    .getMethodsByName("longerMethod")
                    .get(0)
                    .setBlockComment("Lorem ipsum dolor sit amet, consetetur sadipscing elitr.");

            compilationUnit.getClassByName("Foo").get()
                    .getFieldByName("myFoo")
                    .get()
                    .setLineComment("sed diam nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat");

            String expectedCode = readExample("FixIndentOfMovedNodeExpected");
            assertEquals(expectedCode, LexicalPreservingPrinter.print(compilationUnit));
        } catch (IOException ex) {
            fail("Could not read test code", ex);
        }
    }

    @Test
    void issue1321() {
        CompilationUnit compilationUnit = parse("class X { X() {} private void testme() {} }");
        LexicalPreservingPrinter.setup(compilationUnit);

        ClassOrInterfaceDeclaration type = compilationUnit.getClassByName("X").get();
        type.getConstructors().get(0).setBody(new BlockStmt().addStatement("testme();"));

        assertEqualsStringIgnoringEol("class X { X() {\n    testme();\n} private void testme() {} }",
                LexicalPreservingPrinter.print(compilationUnit));
    }

    @Test
    void issue2001() {
        CompilationUnit compilationUnit = parse("class X {void blubb(){X.p(\"blaubb04\");}}");
        LexicalPreservingPrinter.setup(compilationUnit);

        compilationUnit
                .findAll(MethodCallExpr.class)
                .forEach(Node::removeForced);

        assertEqualsStringIgnoringEol("class X {void blubb(){}}", LexicalPreservingPrinter.print(compilationUnit));
    }

    @Test
    void testIndentOfCodeBlocks() throws IOException {
        CompilationUnit compilationUnit = parse(considerExample("IndentOfInsertedCodeBlocks"));
        LexicalPreservingPrinter.setup(compilationUnit);

        IfStmt ifStmt = new IfStmt();
        ifStmt.setCondition(StaticJavaParser.parseExpression("name.equals(\"foo\")"));
        BlockStmt blockStmt = new BlockStmt();
        blockStmt.addStatement(StaticJavaParser.parseStatement("int i = 0;"));
        blockStmt.addStatement(StaticJavaParser.parseStatement("System.out.println(i);"));
        blockStmt.addStatement(
                new IfStmt().setCondition(StaticJavaParser.parseExpression("i < 0"))
                        .setThenStmt(new BlockStmt().addStatement(StaticJavaParser.parseStatement("i = 0;"))));
        blockStmt.addStatement(StaticJavaParser.parseStatement("new Object(){};"));
        ifStmt.setThenStmt(blockStmt);
        ifStmt.setElseStmt(new BlockStmt());

        compilationUnit.findFirst(BlockStmt.class).get().addStatement(ifStmt);
        String expected = considerExample("IndentOfInsertedCodeBlocksExpected");
        TestUtils.assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(compilationUnit));
    }

    @Test
    void commentAddedAtTopLevel() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));
        CompilationUnit cu = javaParser.parse("package x;class X{}").getResult().get();

        cu.setComment(new LineComment("Bla"));
        assertEqualsStringIgnoringEol("//Bla\npackage x;class X{}", LexicalPreservingPrinter.print(cu));

        cu.setComment(new LineComment("BlaBla"));
        assertEqualsStringIgnoringEol("//BlaBla\npackage x;class X{}", LexicalPreservingPrinter.print(cu));

        cu.removeComment();
        assertEqualsStringIgnoringEol("package x;class X{}", LexicalPreservingPrinter.print(cu));
    }

    @Test
    public void testReplaceStringLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        final String code = "\"asd\"";
        final String expected = "\"REPLACEMENT\"";

        final Expression b = javaParser.parseExpression(code).getResult().orElseThrow(AssertionError::new);

        assertTrue(b.isStringLiteralExpr());
        StringLiteralExpr sle = (StringLiteralExpr) b;
        sle.setValue("REPLACEMENT");

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceStringLiteralWithinStatement() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "String str = \"aaa\";";
        String expected = "String str = \"REPLACEMENT\";";

        Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(StringLiteralExpr.class).forEach(stringLiteralExpr -> {
            stringLiteralExpr.setValue("REPLACEMENT");
        });

        assertEquals(expected, LexicalPreservingPrinter.print(b));
        assertEquals(expected, b.toString());
    }

    @Test
    public void testReplaceClassName() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        final String code = "class A {}";
        final CompilationUnit b = javaParser.parse(code).getResult().orElseThrow(AssertionError::new);
        LexicalPreservingPrinter.setup(b);

        assertEquals(1, b.findAll(ClassOrInterfaceDeclaration.class).size());
        b.findAll(ClassOrInterfaceDeclaration.class).forEach(coid -> coid.setName("B"));

        final String expected = "class B {}";

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceIntLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        final String code = "5";
        final String expected = "10";

        final Expression b = javaParser.parseExpression(code).getResult().orElseThrow(AssertionError::new);

        assertTrue(b.isIntegerLiteralExpr());
        ((IntegerLiteralExpr) b).setValue("10");

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceLongLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "long x = 5L;";
        String expected = "long x = 10L;";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(LongLiteralExpr.class).forEach(longLiteralExpr -> {
            longLiteralExpr.setValue("10L");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceBooleanLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "boolean x = true;";
        String expected = "boolean x = false;";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(BooleanLiteralExpr.class).forEach(booleanLiteralExpr -> {
            booleanLiteralExpr.setValue(false);
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceDoubleLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "double x = 5.0D;";
        String expected = "double x = 10.0D;";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(DoubleLiteralExpr.class).forEach(doubleLiteralExpr -> {
            doubleLiteralExpr.setValue("10.0D");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceCharLiteral() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "char x = 'a';";
        String expected = "char x = 'b';";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(CharLiteralExpr.class).forEach(charLiteralExpr -> {
            charLiteralExpr.setValue("b");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceCharLiteralUnicode() {
        final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLexicalPreservationEnabled(true));

        String code = "char x = 'a';";
        String expected = "char x = '\\u0000';";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(CharLiteralExpr.class).forEach(charLiteralExpr -> {
            charLiteralExpr.setValue("\\u0000");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void testReplaceTextBlockLiteral() {
        final JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLexicalPreservationEnabled(true)
                        .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_14)
        );

        String code = "String x = \"\"\"a\"\"\";";
        String expected = "String x = \"\"\"\n" +
                "     REPLACEMENT\n" +
                "     \"\"\";";

        final Statement b = javaParser.parseStatement(code).getResult().orElseThrow(AssertionError::new);
        b.findAll(TextBlockLiteralExpr.class).forEach(textblockLiteralExpr -> {
            textblockLiteralExpr.setValue("\n     REPLACEMENT\n     ");
        });

        final String actual = LexicalPreservingPrinter.print(b);
        assertEquals(expected, actual);
    }

    @Test
    public void removeAnnotationsTest() {
        final JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLexicalPreservationEnabled(true)
        );

//        String eol = EOL;
        String eol = "\n"; // Used to fail on Windows due to not matching line separators within the CSM / difference logic

        String code = "" +
                "public class AssertStmt extends Statement {" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {" + eol +
                "        return v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.MainConstructorGenerator\")" + eol +
                "    public AssertStmt(TokenRange tokenRange, Expression check, Expression message) {" + eol +
                "        super(tokenRange);" + eol +
                "        setCheck(check);" + eol +
                "        setMessage(message);" + eol +
                "        customInitialization();" + eol +
                "    }" + eol +
                "}" + eol +
                "";

        String expected = "" +
                "public class AssertStmt extends Statement {" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {" + eol +
                "        return v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.MainConstructorGenerator\")" + eol +
                "    public AssertStmt(TokenRange tokenRange, Expression check, Expression message) {" + eol +
                "        super(tokenRange);" + eol +
                "        setCheck(check);" + eol +
                "        setMessage(message);" + eol +
                "        customInitialization();" + eol +
                "    }" + eol +
                "}" + eol +
                "";

        final Node b = javaParser.parse(code)
                .getResult()
                .orElseThrow(AssertionError::new);

        List<AnnotationExpr> allAnnotations = b.findAll(AnnotationExpr.class);

        List<Node> annotatedNodes = allAnnotations.stream()
                .filter(annotationExpr -> annotationExpr.getParentNode().isPresent())
                .map(annotationExpr -> annotationExpr.getParentNode().get())
                .collect(Collectors.toList());

        annotatedNodes.stream()
                .filter(node -> node instanceof NodeWithAnnotations)
                .map(node -> (NodeWithAnnotations<?>) node)
                .forEach(nodeWithAnnotations -> {
                    NodeList<AnnotationExpr> annotations = nodeWithAnnotations.getAnnotations();

                    NodeList<AnnotationExpr> newAnnotations = annotations.stream()
//                            .filter(annotationExpr -> !annotationExpr.getName().asString().equals(Override.class.getSimpleName()))
                            .filter(annotationExpr -> !annotationExpr.getName().asString().equals(Generated.class.getSimpleName()))
                            .collect(Collectors.toCollection(NodeList::new));

//                    nodeWithAnnotations.setAnnotations(new NodeList<>());
                    nodeWithAnnotations.setAnnotations(newAnnotations);
                });


        final String actual = LexicalPreservingPrinter.print(b);
        System.out.println(actual);
        assertEqualsStringIgnoringEol(expected, actual);

//        // toString still uses the pretty printer -- avoid within this test...
//        final String actual2 = b.toString();
//        System.out.println(actual2);
//        assertEqualsStringIgnoringEol(expected, actual2);
    }

    @Test
    public void removeAnnotationsTest_fullClass() {
        final JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLexicalPreservationEnabled(true)
        );

        String eol = SYSTEM_EOL;
//        String eol = "\n"; // Used to fail on Windows due to not matching line separators within the CSM / difference logic

        String code = "" +
                "/*" + eol +
                " * Copyright (C) 2007-2010 Júlio Vilmar Gesser." + eol +
                " * Copyright (C) 2011, 2013-2020 The JavaParser Team." + eol +
                " *" + eol +
                " * This file is part of JavaParser." + eol +
                " *" + eol +
                " * JavaParser can be used either under the terms of" + eol +
                " * a) the GNU Lesser General Public License as published by" + eol +
                " *     the Free Software Foundation, either version 3 of the License, or" + eol +
                " *     (at your option) any later version." + eol +
                " * b) the terms of the Apache License" + eol +
                " *" + eol +
                " * You should have received a copy of both licenses in LICENCE.LGPL and" + eol +
                " * LICENCE.APACHE. Please refer to those files for details." + eol +
                " *" + eol +
                " * JavaParser is distributed in the hope that it will be useful," + eol +
                " * but WITHOUT ANY WARRANTY; without even the implied warranty of" + eol +
                " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the" + eol +
                " * GNU Lesser General Public License for more details." + eol +
                " */" + eol +
                "package com.github.javaparser.ast.modules;" + eol +
                "" + eol +
                "import com.github.javaparser.ast.AllFieldsConstructor;" + eol +
                "import com.github.javaparser.ast.Node;" + eol +
                "import com.github.javaparser.ast.NodeList;" + eol +
                "import com.github.javaparser.ast.expr.Name;" + eol +
                "import com.github.javaparser.ast.nodeTypes.NodeWithName;" + eol +
                "import com.github.javaparser.ast.observer.ObservableProperty;" + eol +
                "import com.github.javaparser.ast.visitor.CloneVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.GenericVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.VoidVisitor;" + eol +
                "import static com.github.javaparser.StaticJavaParser.parseName;" + eol +
                "import static com.github.javaparser.utils.Utils.assertNotNull;" + eol +
                "import com.github.javaparser.TokenRange;" + eol +
                "import java.util.function.Consumer;" + eol +
                "import java.util.Optional;" + eol +
                "import com.github.javaparser.metamodel.ModuleExportsDirectiveMetaModel;" + eol +
                "import com.github.javaparser.metamodel.JavaParserMetaModel;" + eol +
                "import com.github.javaparser.ast.Generated;" + eol +
                "" + eol +
                "/**" + eol +
                " * An exports directive in module-info.java. {@code exports R.S to T1.U1, T2.U2;}" + eol +
                " */" + eol +
                "public class ModuleExportsDirective extends ModuleDirective implements NodeWithName<ModuleExportsDirective> {" + eol +
                "" + eol +
                "    private Name name;" + eol +
                "" + eol +
                "    private NodeList<Name> moduleNames;" + eol +
                "" + eol +
                "    public ModuleExportsDirective() {" + eol +
                "        this(null, new Name(), new NodeList<>());" + eol +
                "    }" + eol +
                "" + eol +
                "    @AllFieldsConstructor" + eol +
                "    public ModuleExportsDirective(Name name, NodeList<Name> moduleNames) {" + eol +
                "        this(null, name, moduleNames);" + eol +
                "    }" + eol +
                "" + eol +
                "    /**" + eol +
                "     * This constructor is used by the parser and is considered private." + eol +
                "     */" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.MainConstructorGenerator\")" + eol +
                "    public ModuleExportsDirective(TokenRange tokenRange, Name name, NodeList<Name> moduleNames) {" + eol +
                "        super(tokenRange);" + eol +
                "        setName(name);" + eol +
                "        setModuleNames(moduleNames);" + eol +
                "        customInitialization();" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {" + eol +
                "        return v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <A> void accept(final VoidVisitor<A> v, final A arg) {" + eol +
                "        v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.RemoveMethodGenerator\")" + eol +
                "    public boolean remove(Node node) {" + eol +
                "        if (node == null)" + eol +
                "            return false;" + eol +
                "        for (int i = 0; i < moduleNames.size(); i++) {" + eol +
                "            if (moduleNames.get(i) == node) {" + eol +
                "                moduleNames.remove(i);" + eol +
                "                return true;" + eol +
                "            }" + eol +
                "        }" + eol +
                "        return super.remove(node);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public Name getName() {" + eol +
                "        return name;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public ModuleExportsDirective setName(final Name name) {" + eol +
                "        assertNotNull(name);" + eol +
                "        if (name == this.name) {" + eol +
                "            return (ModuleExportsDirective) this;" + eol +
                "        }" + eol +
                "        notifyPropertyChange(ObservableProperty.NAME, this.name, name);" + eol +
                "        if (this.name != null)" + eol +
                "            this.name.setParentNode(null);" + eol +
                "        this.name = name;" + eol +
                "        setAsParentNodeOf(name);" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public NodeList<Name> getModuleNames() {" + eol +
                "        return moduleNames;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public ModuleExportsDirective setModuleNames(final NodeList<Name> moduleNames) {" + eol +
                "        assertNotNull(moduleNames);" + eol +
                "        if (moduleNames == this.moduleNames) {" + eol +
                "            return (ModuleExportsDirective) this;" + eol +
                "        }" + eol +
                "        notifyPropertyChange(ObservableProperty.MODULE_NAMES, this.moduleNames, moduleNames);" + eol +
                "        if (this.moduleNames != null)" + eol +
                "            this.moduleNames.setParentNode(null);" + eol +
                "        this.moduleNames = moduleNames;" + eol +
                "        setAsParentNodeOf(moduleNames);" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.CloneGenerator\")" + eol +
                "    public ModuleExportsDirective clone() {" + eol +
                "        return (ModuleExportsDirective) accept(new CloneVisitor(), null);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.ReplaceMethodGenerator\")" + eol +
                "    public boolean replace(Node node, Node replacementNode) {" + eol +
                "        if (node == null)" + eol +
                "            return false;" + eol +
                "        for (int i = 0; i < moduleNames.size(); i++) {" + eol +
                "            if (moduleNames.get(i) == node) {" + eol +
                "                moduleNames.set(i, (Name) replacementNode);" + eol +
                "                return true;" + eol +
                "            }" + eol +
                "        }" + eol +
                "        if (node == name) {" + eol +
                "            setName((Name) replacementNode);" + eol +
                "            return true;" + eol +
                "        }" + eol +
                "        return super.replace(node, replacementNode);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public boolean isModuleExportsStmt() {" + eol +
                "        return true;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public ModuleExportsDirective asModuleExportsStmt() {" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public void ifModuleExportsStmt(Consumer<ModuleExportsDirective> action) {" + eol +
                "        action.accept(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public Optional<ModuleExportsDirective> toModuleExportsStmt() {" + eol +
                "        return Optional.of(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    public ModuleExportsDirective addModuleName(String name) {" + eol +
                "        moduleNames.add(parseName(name));" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public boolean isModuleExportsDirective() {" + eol +
                "        return true;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public ModuleExportsDirective asModuleExportsDirective() {" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public Optional<ModuleExportsDirective> toModuleExportsDirective() {" + eol +
                "        return Optional.of(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public void ifModuleExportsDirective(Consumer<ModuleExportsDirective> action) {" + eol +
                "        action.accept(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
                "    @Generated(\"com.github.javaparser.generator.core.node.GetMetaModelGenerator\")" + eol +
                "    public ModuleExportsDirectiveMetaModel getMetaModel() {" + eol +
                "        return JavaParserMetaModel.moduleExportsDirectiveMetaModel;" + eol +
                "    }" + eol +
                "}" + eol + eol +
                "";

        String expected = "" +
                "/*" + eol +
                " * Copyright (C) 2007-2010 Júlio Vilmar Gesser." + eol +
                " * Copyright (C) 2011, 2013-2020 The JavaParser Team." + eol +
                " *" + eol +
                " * This file is part of JavaParser." + eol +
                " *" + eol +
                " * JavaParser can be used either under the terms of" + eol +
                " * a) the GNU Lesser General Public License as published by" + eol +
                " *     the Free Software Foundation, either version 3 of the License, or" + eol +
                " *     (at your option) any later version." + eol +
                " * b) the terms of the Apache License" + eol +
                " *" + eol +
                " * You should have received a copy of both licenses in LICENCE.LGPL and" + eol +
                " * LICENCE.APACHE. Please refer to those files for details." + eol +
                " *" + eol +
                " * JavaParser is distributed in the hope that it will be useful," + eol +
                " * but WITHOUT ANY WARRANTY; without even the implied warranty of" + eol +
                " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the" + eol +
                " * GNU Lesser General Public License for more details." + eol +
                " */" + eol +
                "package com.github.javaparser.ast.modules;" + eol +
                "" + eol +
                "import com.github.javaparser.ast.AllFieldsConstructor;" + eol +
                "import com.github.javaparser.ast.Node;" + eol +
                "import com.github.javaparser.ast.NodeList;" + eol +
                "import com.github.javaparser.ast.expr.Name;" + eol +
                "import com.github.javaparser.ast.nodeTypes.NodeWithName;" + eol +
                "import com.github.javaparser.ast.observer.ObservableProperty;" + eol +
                "import com.github.javaparser.ast.visitor.CloneVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.GenericVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.VoidVisitor;" + eol +
                "import static com.github.javaparser.StaticJavaParser.parseName;" + eol +
                "import static com.github.javaparser.utils.Utils.assertNotNull;" + eol +
                "import com.github.javaparser.TokenRange;" + eol +
                "import java.util.function.Consumer;" + eol +
                "import java.util.Optional;" + eol +
                "import com.github.javaparser.metamodel.ModuleExportsDirectiveMetaModel;" + eol +
                "import com.github.javaparser.metamodel.JavaParserMetaModel;" + eol +
                "import com.github.javaparser.ast.Generated;" + eol +
                "" + eol +
                "/**" + eol +
                " * An exports directive in module-info.java. {@code exports R.S to T1.U1, T2.U2;}" + eol +
                " */" + eol +
                "public class ModuleExportsDirective extends ModuleDirective implements NodeWithName<ModuleExportsDirective> {" + eol +
                "" + eol +
                "    private Name name;" + eol +
                "" + eol +
                "    private NodeList<Name> moduleNames;" + eol +
                "" + eol +
                "    public ModuleExportsDirective() {" + eol +
                "        this(null, new Name(), new NodeList<>());" + eol +
                "    }" + eol +
                "" + eol +
                "    @AllFieldsConstructor" + eol +
                "    public ModuleExportsDirective(Name name, NodeList<Name> moduleNames) {" + eol +
                "        this(null, name, moduleNames);" + eol +
                "    }" + eol +
                "" + eol +
                "    /**" + eol +
                "     * This constructor is used by the parser and is considered private." + eol +
                "     */" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.MainConstructorGenerator\")" + eol +
                "    public ModuleExportsDirective(TokenRange tokenRange, Name name, NodeList<Name> moduleNames) {" + eol +
                "        super(tokenRange);" + eol +
                "        setName(name);" + eol +
                "        setModuleNames(moduleNames);" + eol +
                "        customInitialization();" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {" + eol +
                "        return v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.AcceptGenerator\")" + eol +
                "    public <A> void accept(final VoidVisitor<A> v, final A arg) {" + eol +
                "        v.visit(this, arg);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.RemoveMethodGenerator\")" + eol +
                "    public boolean remove(Node node) {" + eol +
                "        if (node == null)" + eol +
                "            return false;" + eol +
                "        for (int i = 0; i < moduleNames.size(); i++) {" + eol +
                "            if (moduleNames.get(i) == node) {" + eol +
                "                moduleNames.remove(i);" + eol +
                "                return true;" + eol +
                "            }" + eol +
                "        }" + eol +
                "        return super.remove(node);" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public Name getName() {" + eol +
                "        return name;" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public ModuleExportsDirective setName(final Name name) {" + eol +
                "        assertNotNull(name);" + eol +
                "        if (name == this.name) {" + eol +
                "            return (ModuleExportsDirective) this;" + eol +
                "        }" + eol +
                "        notifyPropertyChange(ObservableProperty.NAME, this.name, name);" + eol +
                "        if (this.name != null)" + eol +
                "            this.name.setParentNode(null);" + eol +
                "        this.name = name;" + eol +
                "        setAsParentNodeOf(name);" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public NodeList<Name> getModuleNames() {" + eol +
                "        return moduleNames;" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")" + eol +
                "    public ModuleExportsDirective setModuleNames(final NodeList<Name> moduleNames) {" + eol +
                "        assertNotNull(moduleNames);" + eol +
                "        if (moduleNames == this.moduleNames) {" + eol +
                "            return (ModuleExportsDirective) this;" + eol +
                "        }" + eol +
                "        notifyPropertyChange(ObservableProperty.MODULE_NAMES, this.moduleNames, moduleNames);" + eol +
                "        if (this.moduleNames != null)" + eol +
                "            this.moduleNames.setParentNode(null);" + eol +
                "        this.moduleNames = moduleNames;" + eol +
                "        setAsParentNodeOf(moduleNames);" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.CloneGenerator\")" + eol +
                "    public ModuleExportsDirective clone() {" + eol +
                "        return (ModuleExportsDirective) accept(new CloneVisitor(), null);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.ReplaceMethodGenerator\")" + eol +
                "    public boolean replace(Node node, Node replacementNode) {" + eol +
                "        if (node == null)" + eol +
                "            return false;" + eol +
                "        for (int i = 0; i < moduleNames.size(); i++) {" + eol +
                "            if (moduleNames.get(i) == node) {" + eol +
                "                moduleNames.set(i, (Name) replacementNode);" + eol +
                "                return true;" + eol +
                "            }" + eol +
                "        }" + eol +
                "        if (node == name) {" + eol +
                "            setName((Name) replacementNode);" + eol +
                "            return true;" + eol +
                "        }" + eol +
                "        return super.replace(node, replacementNode);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public boolean isModuleExportsStmt() {" + eol +
                "        return true;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public ModuleExportsDirective asModuleExportsStmt() {" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public void ifModuleExportsStmt(Consumer<ModuleExportsDirective> action) {" + eol +
                "        action.accept(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public Optional<ModuleExportsDirective> toModuleExportsStmt() {" + eol +
                "        return Optional.of(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    public ModuleExportsDirective addModuleName(String name) {" + eol +
                "        moduleNames.add(parseName(name));" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public boolean isModuleExportsDirective() {" + eol +
                "        return true;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public ModuleExportsDirective asModuleExportsDirective() {" + eol +
                "        return this;" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public Optional<ModuleExportsDirective> toModuleExportsDirective() {" + eol +
                "        return Optional.of(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.TypeCastingGenerator\")" + eol +
                "    public void ifModuleExportsDirective(Consumer<ModuleExportsDirective> action) {" + eol +
                "        action.accept(this);" + eol +
                "    }" + eol +
                "" + eol +
                "    @Override" + eol +
//                "    @Generated(\"com.github.javaparser.generator.core.node.GetMetaModelGenerator\")" + eol +
                "    public ModuleExportsDirectiveMetaModel getMetaModel() {" + eol +
                "        return JavaParserMetaModel.moduleExportsDirectiveMetaModel;" + eol +
                "    }" + eol +
                "}" + eol + eol +
                "";

        final Node b = javaParser.parse(code)
                .getResult()
                .orElseThrow(AssertionError::new);

        List<AnnotationExpr> allAnnotations = b.findAll(AnnotationExpr.class);

        List<Node> annotatedNodes = allAnnotations.stream()
                .filter(annotationExpr -> annotationExpr.getParentNode().isPresent())
                .map(annotationExpr -> annotationExpr.getParentNode().get())
                .collect(Collectors.toList());

        annotatedNodes.stream()
                .filter(node -> node instanceof NodeWithAnnotations)
                .map(node -> (NodeWithAnnotations<?>) node)
                .forEach(nodeWithAnnotations -> {
                    NodeList<AnnotationExpr> annotations = nodeWithAnnotations.getAnnotations();

                    NodeList<AnnotationExpr> newAnnotations = annotations.stream()
//                            .filter(annotationExpr -> !annotationExpr.getName().asString().equals(Override.class.getSimpleName()))
                            .filter(annotationExpr -> !annotationExpr.getName().asString().equals(Generated.class.getSimpleName()))
                            .collect(Collectors.toCollection(NodeList::new));

//                    nodeWithAnnotations.setAnnotations(new NodeList<>());
                    nodeWithAnnotations.setAnnotations(newAnnotations);
                });


        final String actual = LexicalPreservingPrinter.print(b);
        System.out.println(actual);
        assertEqualsStringIgnoringEol(expected, actual);

//        // toString still uses the pretty printer -- avoid within this test...
//        final String actual2 = b.toString();
//        System.out.println(actual2);
//        assertEqualsStringIgnoringEol(expected, actual2);
    }

    @Disabled("Exploratory test")
    @Test
    public void addEnumConstantDeclaration() {
        final JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLexicalPreservationEnabled(true)
        );

        String eol = SYSTEM_EOL;
//        String eol = "\n"; // Used to fail on Windows due to not matching line separators within the CSM / difference logic

        String code = "" +
                "/*\n" +
                " * Copyright (C) 2007-2010 Júlio Vilmar Gesser.\n" +
                " * Copyright (C) 2011, 2013-2020 The JavaParser Team.\n" +
                " *\n" +
                " * This file is part of JavaParser.\n" +
                " *\n" +
                " * JavaParser can be used either under the terms of\n" +
                " * a) the GNU Lesser General Public License as published by\n" +
                " *     the Free Software Foundation, either version 3 of the License, or\n" +
                " *     (at your option) any later version.\n" +
                " * b) the terms of the Apache License\n" +
                " *\n" +
                " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
                " * LICENCE.APACHE. Please refer to those files for details.\n" +
                " *\n" +
                " * JavaParser is distributed in the hope that it will be useful,\n" +
                " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
                " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
                " * GNU Lesser General Public License for more details.\n" +
                " */\n" +
                "package com.github.javaparser.ast.observer;\n" +
                "\n" +
                "import com.github.javaparser.ast.Generated;\n" +
                "import com.github.javaparser.ast.Node;\n" +
                "import com.github.javaparser.ast.NodeList;\n" +
                "import com.github.javaparser.utils.Utils;\n" +
                "\n" +
                "import java.lang.reflect.InvocationTargetException;\n" +
                "import java.util.Arrays;\n" +
                "import java.util.Collection;\n" +
                "import java.util.Optional;\n" +
                "\n" +
                "/**\n" +
                " * Properties considered by the AstObserver\n" +
                " */\n" +
                "@Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")\n" +
                "public enum ObservableProperty {\n" +
                "\n" +
                "    ANNOTATIONS(Type.MULTIPLE_REFERENCE),\n" +
                "    ANONYMOUS_CLASS_BODY(Type.MULTIPLE_REFERENCE),\n" +
                "    ARGUMENTS(Type.MULTIPLE_REFERENCE),\n" +
                "    ASTERISK(Type.SINGLE_ATTRIBUTE),\n" +
                "    BODY(Type.SINGLE_REFERENCE),\n" +
                "    CATCH_CLAUSES(Type.MULTIPLE_REFERENCE),\n" +
                "    CHECK(Type.SINGLE_REFERENCE),\n" +
                "    CLASS_BODY(Type.MULTIPLE_REFERENCE),\n" +
                "    CLASS_DECLARATION(Type.SINGLE_REFERENCE),\n" +
                "    COMMENT(Type.SINGLE_REFERENCE),\n" +
                "    COMPARE(Type.SINGLE_REFERENCE),\n" +
                "    COMPONENT_TYPE(Type.SINGLE_REFERENCE),\n" +
                "    CONDITION(Type.SINGLE_REFERENCE),\n" +
                "    CONTENT(Type.SINGLE_ATTRIBUTE),\n" +
                "    DEFAULT_VALUE(Type.SINGLE_REFERENCE),\n" +
                "    DIMENSION(Type.SINGLE_REFERENCE),\n" +
                "    DIRECTIVES(Type.MULTIPLE_REFERENCE),\n" +
                "    ELEMENTS(Type.MULTIPLE_REFERENCE),\n" +
                "    ELEMENT_TYPE(Type.SINGLE_REFERENCE),\n" +
                "    ELSE_EXPR(Type.SINGLE_REFERENCE),\n" +
                "    ELSE_STMT(Type.SINGLE_REFERENCE),\n" +
                "    ENCLOSING_PARAMETERS(Type.SINGLE_ATTRIBUTE),\n" +
                "    ENTRIES(Type.MULTIPLE_REFERENCE),\n" +
                "    EXPRESSION(Type.SINGLE_REFERENCE),\n" +
                "    EXTENDED_TYPE(Type.SINGLE_REFERENCE),\n" +
                "    EXTENDED_TYPES(Type.MULTIPLE_REFERENCE),\n" +
                "    FINALLY_BLOCK(Type.SINGLE_REFERENCE),\n" +
                "    IDENTIFIER(Type.SINGLE_ATTRIBUTE),\n" +
                "    IMPLEMENTED_TYPES(Type.MULTIPLE_REFERENCE),\n" +
                "    IMPORTS(Type.MULTIPLE_REFERENCE),\n" +
                "    INDEX(Type.SINGLE_REFERENCE),\n" +
                "    INITIALIZATION(Type.MULTIPLE_REFERENCE),\n" +
                "    INITIALIZER(Type.SINGLE_REFERENCE),\n" +
                "    INNER(Type.SINGLE_REFERENCE),\n" +
                "    INTERFACE(Type.SINGLE_ATTRIBUTE),\n" +
                "    ITERABLE(Type.SINGLE_REFERENCE),\n" +
                "    KEYWORD(Type.SINGLE_ATTRIBUTE),\n" +
                "    LABEL(Type.SINGLE_REFERENCE),\n" +
                "    LABELS(Type.MULTIPLE_REFERENCE),\n" +
                "    LEFT(Type.SINGLE_REFERENCE),\n" +
                "    LEVELS(Type.MULTIPLE_REFERENCE),\n" +
                "    MEMBERS(Type.MULTIPLE_REFERENCE),\n" +
                "    MEMBER_VALUE(Type.SINGLE_REFERENCE),\n" +
                "    MESSAGE(Type.SINGLE_REFERENCE),\n" +
                "    MODIFIERS(Type.MULTIPLE_REFERENCE),\n" +
                "    MODULE(Type.SINGLE_REFERENCE),\n" +
                "    MODULE_NAMES(Type.MULTIPLE_REFERENCE),\n" +
                "    NAME(Type.SINGLE_REFERENCE),\n" +
                "    OPEN(Type.SINGLE_ATTRIBUTE),\n" +
                "    OPERATOR(Type.SINGLE_ATTRIBUTE),\n" +
                "    ORIGIN(Type.SINGLE_ATTRIBUTE),\n" +
                "    PACKAGE_DECLARATION(Type.SINGLE_REFERENCE),\n" +
                "    PAIRS(Type.MULTIPLE_REFERENCE),\n" +
                "    PARAMETER(Type.SINGLE_REFERENCE),\n" +
                "    PARAMETERS(Type.MULTIPLE_REFERENCE),\n" +
                "    QUALIFIER(Type.SINGLE_REFERENCE),\n" +
                "    RECEIVER_PARAMETER(Type.SINGLE_REFERENCE),\n" +
                "    RESOURCES(Type.MULTIPLE_REFERENCE),\n" +
                "    RIGHT(Type.SINGLE_REFERENCE),\n" +
                "    SCOPE(Type.SINGLE_REFERENCE),\n" +
                "    SELECTOR(Type.SINGLE_REFERENCE),\n" +
                "    STATEMENT(Type.SINGLE_REFERENCE),\n" +
                "    STATEMENTS(Type.MULTIPLE_REFERENCE),\n" +
                "    STATIC(Type.SINGLE_ATTRIBUTE),\n" +
                "    SUPER_TYPE(Type.SINGLE_REFERENCE),\n" +
                "    TARGET(Type.SINGLE_REFERENCE),\n" +
                "    THEN_EXPR(Type.SINGLE_REFERENCE),\n" +
                "    THEN_STMT(Type.SINGLE_REFERENCE),\n" +
                "    THIS(Type.SINGLE_ATTRIBUTE),\n" +
                "    THROWN_EXCEPTIONS(Type.MULTIPLE_REFERENCE),\n" +
                "    TRY_BLOCK(Type.SINGLE_REFERENCE),\n" +
                "    TYPE(Type.SINGLE_REFERENCE),\n" +
                "    TYPES(Type.MULTIPLE_REFERENCE),\n" +
                "    TYPE_ARGUMENTS(Type.MULTIPLE_REFERENCE),\n" +
                "    TYPE_BOUND(Type.MULTIPLE_REFERENCE),\n" +
                "    TYPE_NAME(Type.SINGLE_REFERENCE),\n" +
                "    TYPE_PARAMETERS(Type.MULTIPLE_REFERENCE),\n" +
                "    UPDATE(Type.MULTIPLE_REFERENCE),\n" +
                "    VALUE(Type.SINGLE_REFERENCE),\n" +
                "    VALUES(Type.MULTIPLE_REFERENCE),\n" +
                "    VARIABLE(Type.SINGLE_REFERENCE),\n" +
                "    VARIABLES(Type.MULTIPLE_REFERENCE),\n" +
                "    VAR_ARGS(Type.SINGLE_ATTRIBUTE),\n" +
                "    VAR_ARGS_ANNOTATIONS(Type.MULTIPLE_REFERENCE),\n" +
                "    WITH(Type.MULTIPLE_REFERENCE),\n" +
                "    CASCADING_IF_STMT(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    ELSE_BLOCK(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    ELSE_BRANCH(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    EXPRESSION_BODY(Type.SINGLE_REFERENCE, true),\n" +
                "    MAXIMUM_COMMON_TYPE(Type.SINGLE_REFERENCE, true),\n" +
                "    POSTFIX(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    PREFIX(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    THEN_BLOCK(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    USING_DIAMOND_OPERATOR(Type.SINGLE_ATTRIBUTE, true),\n" +
                "    RANGE,\n" +
                "    COMMENTED_NODE;\n" +
                "\n" +
                "    private final boolean derived;\n" +
                "    private final Type type;\n" +
                "\n" +
                "    ObservableProperty(Type type) {\n" +
                "        this.type = type;\n" +
                "        this.derived = false;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty(Type type, boolean derived) {\n" +
                "        this.type = type;\n" +
                "        this.derived = derived;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty() {\n" +
                "        this(Type.SINGLE_REFERENCE, false);\n" +
                "    }\n" +
                "\n" +
                "    public static ObservableProperty fromCamelCaseName(String camelCaseName) {\n" +
                "        Optional<ObservableProperty> observableProperty = Arrays.stream(values()).filter(v -> v.camelCaseName().equals(camelCaseName)).findFirst();\n" +
                "        if (observableProperty.isPresent()) {\n" +
                "            return observableProperty.get();\n" +
                "        } else {\n" +
                "            throw new IllegalArgumentException(\"No property found with the given camel case name: \" + camelCaseName);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String camelCaseName() {\n" +
                "        return Utils.screamingToCamelCase(name());\n" +
                "    }\n" +
                "\n" +
                "    public Object getRawValue(Node node) {\n" +
                "        String getterName = \"get\" + Utils.capitalize(camelCaseName());\n" +
                "        if (!hasMethod(node, getterName)) {\n" +
                "            getterName = \"is\" + Utils.capitalize(camelCaseName());\n" +
                "            if (!hasMethod(node, getterName)) {\n" +
                "                getterName = \"has\" + Utils.capitalize(camelCaseName());\n" +
                "            }\n" +
                "        }\n" +
                "        try {\n" +
                "            return node.getClass().getMethod(getterName).invoke(node);\n" +
                "        } catch (NoSuchMethodException | IllegalAccessException | InvocationTargetException e) {\n" +
                "            throw new RuntimeException(\"Unable to get value for \" + this.name() + \" from \" + node + \" (\" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Boolean getValueAsBooleanAttribute(Node node) {\n" +
                "        return (Boolean) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public Collection<?> getValueAsCollection(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            return (Collection) rawValue;\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public NodeList<? extends Node> getValueAsMultipleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue == null) {\n" +
                "                return null;\n" +
                "            }\n" +
                "            if (rawValue instanceof NodeList) {\n" +
                "                return (NodeList) rawValue;\n" +
                "            } else {\n" +
                "                Optional<NodeList> opt = (Optional<NodeList>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Node getValueAsSingleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue instanceof Node) {\n" +
                "                return (Node) rawValue;\n" +
                "            } else if (rawValue instanceof Optional) {\n" +
                "                Optional<Node> opt = (Optional<Node>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            } else {\n" +
                "                throw new RuntimeException(String.format(\"Property %s returned %s (%s)\", this.name(), rawValue.toString(), rawValue.getClass().getCanonicalName()));\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String getValueAsStringAttribute(Node node) {\n" +
                "        return (String) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    private boolean hasMethod(Node node, String name) {\n" +
                "        try {\n" +
                "            node.getClass().getMethod(name);\n" +
                "            return true;\n" +
                "        } catch (NoSuchMethodException e) {\n" +
                "            return false;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutNodes() {\n" +
                "        return type.node;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutValues() {\n" +
                "        return !isAboutNodes();\n" +
                "    }\n" +
                "\n" +
                "    public boolean isDerived() {\n" +
                "        return derived;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isMultiple() {\n" +
                "        return type.multiple;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNull(Node node) {\n" +
                "        return null == getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrEmpty(Node node) {\n" +
                "        return Utils.valueIsNullOrEmpty(getRawValue(node));\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrNotPresent(Node node) {\n" +
                "        Object result = getRawValue(node);\n" +
                "        if (result == null) {\n" +
                "            return true;\n" +
                "        }\n" +
                "        if (result instanceof Optional) {\n" +
                "            return !((Optional) result).isPresent();\n" +
                "        }\n" +
                "        return false;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isSingle() {\n" +
                "        return !isMultiple();\n" +
                "    }\n" +
                "\n" +
                "    enum Type {\n" +
                "\n" +
                "        SINGLE_ATTRIBUTE(false, false),\n" +
                "        SINGLE_REFERENCE(false, true),\n" +
                "        MULTIPLE_ATTRIBUTE(true, false),\n" +
                "        MULTIPLE_REFERENCE(true, true);\n" +
                "\n" +
                "        private final boolean multiple;\n" +
                "\n" +
                "        private final boolean node;\n" +
                "\n" +
                "        Type(boolean multiple, boolean node) {\n" +
                "            this.multiple = multiple;\n" +
                "            this.node = node;\n" +
                "        }\n" +
                "    }\n" +
                "}\n" +
                "";

        String expected_lexical = "" +
                "@Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")\n" +
                "public enum ObservableProperty {\n" +
                "    ANNOTATIONS(Type.SINGLE_ATTRIBUTE),\n" +
                "    ANONYMOUS_CLASS_BODY(Type.SINGLE_ATTRIBUTE);\n" +
                "\n" +
                "    private final boolean derived;\n" +
                "    private final Type type;\n" +
                "\n" +
                "    ObservableProperty(Type type) {\n" +
                "        this.type = type;\n" +
                "        this.derived = false;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty(Type type, boolean derived) {\n" +
                "        this.type = type;\n" +
                "        this.derived = derived;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty() {\n" +
                "        this(Type.SINGLE_REFERENCE, false);\n" +
                "    }\n" +
                "\n" +
                "    public static ObservableProperty fromCamelCaseName(String camelCaseName) {\n" +
                "        Optional<ObservableProperty> observableProperty = Arrays.stream(values()).filter(v -> v.camelCaseName().equals(camelCaseName)).findFirst();\n" +
                "        if (observableProperty.isPresent()) {\n" +
                "            return observableProperty.get();\n" +
                "        } else {\n" +
                "            throw new IllegalArgumentException(\"No property found with the given camel case name: \" + camelCaseName);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String camelCaseName() {\n" +
                "        return Utils.screamingToCamelCase(name());\n" +
                "    }\n" +
                "\n" +
                "    public Object getRawValue(Node node) {\n" +
                "        String getterName = \"get\" + Utils.capitalize(camelCaseName());\n" +
                "        if (!hasMethod(node, getterName)) {\n" +
                "            getterName = \"is\" + Utils.capitalize(camelCaseName());\n" +
                "            if (!hasMethod(node, getterName)) {\n" +
                "                getterName = \"has\" + Utils.capitalize(camelCaseName());\n" +
                "            }\n" +
                "        }\n" +
                "        try {\n" +
                "            return node.getClass().getMethod(getterName).invoke(node);\n" +
                "        } catch (NoSuchMethodException | IllegalAccessException | InvocationTargetException e) {\n" +
                "            throw new RuntimeException(\"Unable to get value for \" + this.name() + \" from \" + node + \" (\" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Boolean getValueAsBooleanAttribute(Node node) {\n" +
                "        return (Boolean) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public Collection<?> getValueAsCollection(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            return (Collection) rawValue;\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public NodeList<? extends Node> getValueAsMultipleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue == null) {\n" +
                "                return null;\n" +
                "            }\n" +
                "            if (rawValue instanceof NodeList) {\n" +
                "                return (NodeList) rawValue;\n" +
                "            } else {\n" +
                "                Optional<NodeList> opt = (Optional<NodeList>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Node getValueAsSingleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue instanceof Node) {\n" +
                "                return (Node) rawValue;\n" +
                "            } else if (rawValue instanceof Optional) {\n" +
                "                Optional<Node> opt = (Optional<Node>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            } else {\n" +
                "                throw new RuntimeException(String.format(\"Property %s returned %s (%s)\", this.name(), rawValue.toString(), rawValue.getClass().getCanonicalName()));\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String getValueAsStringAttribute(Node node) {\n" +
                "        return (String) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    private boolean hasMethod(Node node, String name) {\n" +
                "        try {\n" +
                "            node.getClass().getMethod(name);\n" +
                "            return true;\n" +
                "        } catch (NoSuchMethodException e) {\n" +
                "            return false;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutNodes() {\n" +
                "        return type.node;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutValues() {\n" +
                "        return !isAboutNodes();\n" +
                "    }\n" +
                "\n" +
                "    public boolean isDerived() {\n" +
                "        return derived;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isMultiple() {\n" +
                "        return type.multiple;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNull(Node node) {\n" +
                "        return null == getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrEmpty(Node node) {\n" +
                "        return Utils.valueIsNullOrEmpty(getRawValue(node));\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrNotPresent(Node node) {\n" +
                "        Object result = getRawValue(node);\n" +
                "        if (result == null) {\n" +
                "            return true;\n" +
                "        }\n" +
                "        if (result instanceof Optional) {\n" +
                "            return !((Optional) result).isPresent();\n" +
                "        }\n" +
                "        return false;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isSingle() {\n" +
                "        return !isMultiple();\n" +
                "    }\n" +
                "\n" +
                "    enum Type {\n" +
                "\n" +
                "        SINGLE_ATTRIBUTE(false, false),\n" +
                "        SINGLE_REFERENCE(false, true),\n" +
                "        MULTIPLE_ATTRIBUTE(true, false),\n" +
                "        MULTIPLE_REFERENCE(true, true);\n" +
                "\n" +
                "        private final boolean multiple;\n" +
                "\n" +
                "        private final boolean node;\n" +
                "\n" +
                "        Type(boolean multiple, boolean node) {\n" +
                "            this.multiple = multiple;\n" +
                "            this.node = node;\n" +
                "        }\n" +
                "    }\n" +
                "}" + // "\n" +
                "";

        String expected_lexical1 = "" +
                "@Generated(\"com.github.javaparser.generator.core.node.PropertyGenerator\")\n" +
                "public enum ObservableProperty {\n" +
                "    ANNOTATIONS(Type.SINGLE_ATTRIBUTE);\n" +
                "\n" +
                "    private final boolean derived;\n" +
                "    private final Type type;\n" +
                "\n" +
                "    ObservableProperty(Type type) {\n" +
                "        this.type = type;\n" +
                "        this.derived = false;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty(Type type, boolean derived) {\n" +
                "        this.type = type;\n" +
                "        this.derived = derived;\n" +
                "    }\n" +
                "\n" +
                "    ObservableProperty() {\n" +
                "        this(Type.SINGLE_REFERENCE, false);\n" +
                "    }\n" +
                "\n" +
                "    public static ObservableProperty fromCamelCaseName(String camelCaseName) {\n" +
                "        Optional<ObservableProperty> observableProperty = Arrays.stream(values()).filter(v -> v.camelCaseName().equals(camelCaseName)).findFirst();\n" +
                "        if (observableProperty.isPresent()) {\n" +
                "            return observableProperty.get();\n" +
                "        } else {\n" +
                "            throw new IllegalArgumentException(\"No property found with the given camel case name: \" + camelCaseName);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String camelCaseName() {\n" +
                "        return Utils.screamingToCamelCase(name());\n" +
                "    }\n" +
                "\n" +
                "    public Object getRawValue(Node node) {\n" +
                "        String getterName = \"get\" + Utils.capitalize(camelCaseName());\n" +
                "        if (!hasMethod(node, getterName)) {\n" +
                "            getterName = \"is\" + Utils.capitalize(camelCaseName());\n" +
                "            if (!hasMethod(node, getterName)) {\n" +
                "                getterName = \"has\" + Utils.capitalize(camelCaseName());\n" +
                "            }\n" +
                "        }\n" +
                "        try {\n" +
                "            return node.getClass().getMethod(getterName).invoke(node);\n" +
                "        } catch (NoSuchMethodException | IllegalAccessException | InvocationTargetException e) {\n" +
                "            throw new RuntimeException(\"Unable to get value for \" + this.name() + \" from \" + node + \" (\" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Boolean getValueAsBooleanAttribute(Node node) {\n" +
                "        return (Boolean) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public Collection<?> getValueAsCollection(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            return (Collection) rawValue;\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public NodeList<? extends Node> getValueAsMultipleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue == null) {\n" +
                "                return null;\n" +
                "            }\n" +
                "            if (rawValue instanceof NodeList) {\n" +
                "                return (NodeList) rawValue;\n" +
                "            } else {\n" +
                "                Optional<NodeList> opt = (Optional<NodeList>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(\"Unable to get list value for \" + this.name() + \" from \" + node + \" (class: \" + node.getClass().getSimpleName() + \")\", e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public Node getValueAsSingleReference(Node node) {\n" +
                "        Object rawValue = getRawValue(node);\n" +
                "        try {\n" +
                "            if (rawValue instanceof Node) {\n" +
                "                return (Node) rawValue;\n" +
                "            } else if (rawValue instanceof Optional) {\n" +
                "                Optional<Node> opt = (Optional<Node>) rawValue;\n" +
                "                if (opt.isPresent()) {\n" +
                "                    return opt.get();\n" +
                "                } else {\n" +
                "                    return null;\n" +
                "                }\n" +
                "            } else {\n" +
                "                throw new RuntimeException(String.format(\"Property %s returned %s (%s)\", this.name(), rawValue.toString(), rawValue.getClass().getCanonicalName()));\n" +
                "            }\n" +
                "        } catch (ClassCastException e) {\n" +
                "            throw new RuntimeException(e);\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public String getValueAsStringAttribute(Node node) {\n" +
                "        return (String) getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    private boolean hasMethod(Node node, String name) {\n" +
                "        try {\n" +
                "            node.getClass().getMethod(name);\n" +
                "            return true;\n" +
                "        } catch (NoSuchMethodException e) {\n" +
                "            return false;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutNodes() {\n" +
                "        return type.node;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isAboutValues() {\n" +
                "        return !isAboutNodes();\n" +
                "    }\n" +
                "\n" +
                "    public boolean isDerived() {\n" +
                "        return derived;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isMultiple() {\n" +
                "        return type.multiple;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNull(Node node) {\n" +
                "        return null == getRawValue(node);\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrEmpty(Node node) {\n" +
                "        return Utils.valueIsNullOrEmpty(getRawValue(node));\n" +
                "    }\n" +
                "\n" +
                "    public boolean isNullOrNotPresent(Node node) {\n" +
                "        Object result = getRawValue(node);\n" +
                "        if (result == null) {\n" +
                "            return true;\n" +
                "        }\n" +
                "        if (result instanceof Optional) {\n" +
                "            return !((Optional) result).isPresent();\n" +
                "        }\n" +
                "        return false;\n" +
                "    }\n" +
                "\n" +
                "    public boolean isSingle() {\n" +
                "        return !isMultiple();\n" +
                "    }\n" +
                "\n" +
                "    enum Type {\n" +
                "\n" +
                "        SINGLE_ATTRIBUTE(false, false),\n" +
                "        SINGLE_REFERENCE(false, true),\n" +
                "        MULTIPLE_ATTRIBUTE(true, false),\n" +
                "        MULTIPLE_REFERENCE(true, true);\n" +
                "\n" +
                "        private final boolean multiple;\n" +
                "\n" +
                "        private final boolean node;\n" +
                "\n" +
                "        Type(boolean multiple, boolean node) {\n" +
                "            this.multiple = multiple;\n" +
                "            this.node = node;\n" +
                "        }\n" +
                "    }\n" +
                "}" + // "\n" +
                "";


        //
        final Node b = javaParser.parse(code).getResult().orElseThrow(AssertionError::new);
        Optional<EnumDeclaration> optionalEnumDeclaration = ((CompilationUnit) b).getEnumByName("ObservableProperty");
        assertTrue(optionalEnumDeclaration.isPresent());
        EnumDeclaration enumDeclaration = optionalEnumDeclaration.get();

        // Clear all the declarations
        enumDeclaration.getEntries().clear();

        //
        EnumConstantDeclaration enumConstantDeclaration;

        // Re-add the one constant
//        enumConstantDeclaration = enumDeclaration.addEnumConstant("ANNOTATIONS");
//        enumConstantDeclaration.addArgument("Type.SINGLE_ATTRIBUTE");
////        assertEqualsStringIgnoringEol(expected_lexical1, LexicalPreservingPrinter.print(enumDeclaration));
//
//        // Re-add a second constant
//        enumConstantDeclaration = enumDeclaration.addEnumConstant("ANONYMOUS_CLASS_BODY");
//        enumConstantDeclaration.addArgument("Type.SINGLE_ATTRIBUTE");
//        enumConstantDeclaration = enumDeclaration.addEnumConstant("ANONYMOUS_CLASS_BODY1");
//        enumConstantDeclaration.addArgument("Type.SINGLE_ATTRIBUTE");
//        enumConstantDeclaration = enumDeclaration.addEnumConstant("ANONYMOUS_CLASS_BODY2");
//        enumConstantDeclaration.addArgument("Type.SINGLE_ATTRIBUTE");
//        enumConstantDeclaration = enumDeclaration.addEnumConstant("ANONYMOUS_CLASS_BODY3");
//        enumConstantDeclaration.addArgument("Type.SINGLE_ATTRIBUTE");
        assertEqualsStringIgnoringEol(expected_lexical, LexicalPreservingPrinter.print(enumDeclaration));



//        //// FIRST CONFIRM THAT THE PRETTY PRINTED VERSION MATCHES EXPECTATIONS
//        final String prettyString = b.toString();
////        System.out.println("Pretty: \n" + prettyString);
////        assertEqualsStringIgnoringEol(expected_pretty, prettyString);
//
//
//        //// NEXT CONFIRM THAT THE LEXICAL PREVERVING PRINTER PRINTS THE SAME
//        TypeDeclaration<?> prettyEnumDeclaration = StaticJavaParser.parseTypeDeclaration(prettyString);
//        String print = LexicalPreservingPrinter.print(prettyEnumDeclaration.asEnumDeclaration());
//
//        System.out.println("Lexical preserving: \n" + print);
//        assertEqualsStringIgnoringEol(expected_lexical, print);

    }


    @Test
    public void addRemoveImportDeclaration() {
        final JavaParser javaParser = new JavaParser(
                new ParserConfiguration()
                        .setLexicalPreservationEnabled(true)
        );

//        String eol = SYSTEM_EOL;
        String eol = "\n"; // Used to fail on Windows due to not matching line separators within the CSM / difference logic

        String code = "" +
                "/*" + eol +
                " * Copyright (C) 2007-2010 Júlio Vilmar Gesser." + eol +
                " * Copyright (C) 2011, 2013-2020 The JavaParser Team." + eol +
                " *" + eol +
                " * This file is part of JavaParser." + eol +
                " *" + eol +
                " * JavaParser can be used either under the terms of" + eol +
                " * a) the GNU Lesser General Public License as published by" + eol +
                " *     the Free Software Foundation, either version 3 of the License, or" + eol +
                " *     (at your option) any later version." + eol +
                " * b) the terms of the Apache License" + eol +
                " *" + eol +
                " * You should have received a copy of both licenses in LICENCE.LGPL and" + eol +
                " * LICENCE.APACHE. Please refer to those files for details." + eol +
                " *" + eol +
                " * JavaParser is distributed in the hope that it will be useful," + eol +
                " * but WITHOUT ANY WARRANTY; without even the implied warranty of" + eol +
                " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the" + eol +
                " * GNU Lesser General Public License for more details." + eol +
                " */" + eol +
                "package com.github.javaparser.ast.modules;" + eol +
                "" + eol +
                "import com.github.javaparser.ast.AllFieldsConstructor;" + eol +
                "import com.github.javaparser.ast.Node;" + eol +
                "import com.github.javaparser.ast.NodeList;" + eol +
                "import com.github.javaparser.ast.expr.Name;" + eol +
                "import com.github.javaparser.ast.nodeTypes.NodeWithName;" + eol +
                "import com.github.javaparser.ast.observer.ObservableProperty;" + eol +
                "import com.github.javaparser.ast.visitor.CloneVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.GenericVisitor;" + eol +
                "import com.github.javaparser.ast.visitor.VoidVisitor;" + eol +
                "import static com.github.javaparser.StaticJavaParser.parseName;" + eol +
                "import static com.github.javaparser.utils.Utils.assertNotNull;" + eol +
                "import com.github.javaparser.TokenRange;" + eol +
                "import java.util.function.Consumer;" + eol +
                "import java.util.Optional;" + eol +
                "import com.github.javaparser.metamodel.ModuleExportsDirectiveMetaModel;" + eol +
                "import com.github.javaparser.metamodel.JavaParserMetaModel;" + eol +
                "import com.github.javaparser.ast.Generated;" + eol +
                "" + eol +
                "/**" + eol +
                " * An exports directive in module-info.java. {@code exports R.S to T1.U1, T2.U2;}" + eol +
                " */" + eol +
                "public class X {" + eol +
                "" + eol +
                "}" + eol +
                "";

        //
        final Node b = javaParser.parse(code).getResult().orElseThrow(AssertionError::new);

        CompilationUnit cu = (CompilationUnit) b;
        LexicalPreservingPrinter.setup(cu);

        Class<StaleGenerated> annotationClass = StaleGenerated.class;

        cu.addImport(annotationClass);
        cu.getImports().removeIf(importDeclaration -> {
            return importDeclaration.getNameAsString().equals(annotationClass.getCanonicalName());
        });
        cu.addImport(annotationClass);
        cu.getImports().removeIf(importDeclaration -> {
            return importDeclaration.getNameAsString().equals(annotationClass.getCanonicalName());
        });

        System.out.println("cu = " + cu);


    }

}
