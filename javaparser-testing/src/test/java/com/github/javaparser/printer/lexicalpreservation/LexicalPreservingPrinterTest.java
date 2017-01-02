package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.*;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.Type;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class LexicalPreservingPrinterTest extends AbstractLexicalPreservingTest {

    //
    // Tests on TextNode definition
    //

    @Test
    public void checkNodeTextCreatedForSimplestClass() {
        considerCode("class A {}");

        // CU
        assertEquals(1, lpp.getTextForNode(cu).numberOfElements());
        assertEquals(true, lpp.getTextForNode(cu).getTextElement(0) instanceof ChildTextElement);
        assertEquals(cu.getClassByName("A").get(), ((ChildTextElement)lpp.getTextForNode(cu).getTextElement(0)).getChild());

        // Class
        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        assertEquals(7, lpp.getTextForNode(classA).numberOfElements());
        assertEquals("class", lpp.getTextForNode(classA).getTextElement(0).expand());
        assertEquals(" ", lpp.getTextForNode(classA).getTextElement(1).expand());
        assertEquals("A", lpp.getTextForNode(classA).getTextElement(2).expand());
        assertEquals(" ", lpp.getTextForNode(classA).getTextElement(3).expand());
        assertEquals("{", lpp.getTextForNode(classA).getTextElement(4).expand());
        assertEquals("}", lpp.getTextForNode(classA).getTextElement(5).expand());
        assertEquals("", lpp.getTextForNode(classA).getTextElement(6).expand());
        assertEquals(true, lpp.getTextForNode(classA).getTextElement(6) instanceof TokenTextElement);
        assertEquals(ASTParserConstants.EOF, ((TokenTextElement)lpp.getTextForNode(classA).getTextElement(6)).getTokenKind());
    }

    @Test
    public void checkNodeTextCreatedForField() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        NodeText nodeText = lpp.getOrCreateNodeText(fd);
        assertEquals(Arrays.asList("int", " ", "i", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForVariableDeclarator() {
        String code = "class A {int i;}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        FieldDeclaration fd = classA.getFieldByName("i").get();
        VariableDeclarator vd = fd.getVariables().get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(vd);
        assertEquals(Arrays.asList("i"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethodParameter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        NodeText nodeText = lpp.getOrCreateNodeText(p1);
        assertEquals(Arrays.asList("int", " ", "p1"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForPrimitiveType() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParameterByName("p1").get();
        Type t = p1.getType();
        NodeText nodeText = lpp.getOrCreateNodeText(t);
        assertEquals(Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForSimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(imp);
        assertEquals(Arrays.asList("import", " ", "a.b.c.D", ";", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedGenericType() {
        String code = "class A {ParseResult<T> result;}";
        considerCode(code);

        FieldDeclaration field = cu.getClassByName("A").get().getFieldByName("result").get();
        Node t = field.getCommonType();
        Node t2 = field.getVariable(0).getType();
        NodeText nodeText = lpp.getOrCreateNodeText(field);
        assertEquals(Arrays.asList("ParseResult", "<", "T", ">", " ", "result", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        NodeText nodeText = lpp.getOrCreateNodeText(ad);
        assertEquals(Arrays.asList("public", " ", "@", "interface", " ", "ClassPreamble", " ", "{", " ", "String author();", " ", "}", ""),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclaration() {
        String code = "public @interface ClassPreamble { String author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "author", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationArrayType() {
        String code = "public @interface ClassPreamble { String[] author(); }";
        considerCode(code);

        AnnotationDeclaration ad = cu.getAnnotationDeclarationByName("ClassPreamble").get();
        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)ad.getMember(0);
        Type type = md.getType();
        NodeText nodeText = lpp.getOrCreateNodeText(type);
        assertEquals(Arrays.asList("String", "[", "]"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");

        AnnotationMemberDeclaration md = (AnnotationMemberDeclaration)cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("String[]", " ", "reviewers", "(", ")", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    //
    // Tests on findIndentation
    //

    @Test
    public void findIndentationForAnnotationMemberDeclarationWithoutComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(4);
        List<TokenTextElement> indentation = lpp.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(e -> e.expand()).collect(Collectors.toList()));
    }

    @Test
    public void findIndentationForAnnotationMemberDeclarationWithComment() throws IOException {
        considerExample("AnnotationDeclaration_Example3_original");
        Node node = cu.getAnnotationDeclarationByName("ClassPreamble").get().getMember(5);
        List<TokenTextElement> indentation = lpp.findIndentation(node);
        assertEquals(Arrays.asList(" ", " ", " "), indentation.stream().map(e -> e.expand()).collect(Collectors.toList()));
    }

    //
    // Tests on printing
    //

    @Test
    public void printASuperSimpleCUWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
    }

    @Test
    public void printASuperSimpleClassWithAFieldAdded() {
        String code = "class A {}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        classA.addField("int", "myField");
        assertEquals("class A {\n    int myField;\n}", lpp.print(classA));
    }

    @Test
    public void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, lpp.print(cu.getClassByName("A").get()));
    }

    @Test
    public void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t\n int f;\n\n\n         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
        assertEquals(code, lpp.print(cu.getClassByName("A").get()));
        assertEquals("void foo(int p  ) { return  'z'  \t; }", lpp.print(cu.getClassByName("A").get().getMethodsByName("foo").get(0)));
    }

    @Test
    public void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t\n int f;\n\n\n         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A").get();
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t\n" +
                "\n" +
                "\n" +
                "         void foo(int p  ) { return  'z'  \t; }}", lpp.print(c));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        m.getParameters().remove(1);
        assertEquals("void foo(char p1) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodAddingAStatement() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        Statement s = new ExpressionStmt(new BinaryExpr(
                new IntegerLiteralExpr("10"), new IntegerLiteralExpr("2"), BinaryExpr.Operator.PLUS
        ));
        NodeList<Statement> stmts = cu.getClassByName("A").get().getMethodsByName("foo").get(0).getBody().get().getStatements();
        stmts.add(s);
        MethodDeclaration m = cu.getClassByName("A").get().getMethodsByName("foo").get(0);
        assertEquals("void foo(char p1, int p2) {\n" +
                "     10 + 2;\n" +
                " }", lpp.print(m));
    }

    @Test
    public void printASimpleImport() {
        String code = "import a.b.c.D;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import a.b.c.D;", lpp.print(imp));
    }

    @Test
    public void printAnotherImport() {
        String code = "import com.github.javaparser.ast.CompilationUnit;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import com.github.javaparser.ast.CompilationUnit;", lpp.print(imp));
    }

    @Test
    public void printAStaticImport() {
        String code = "import static com.github.javaparser.ParseStart.*;";
        considerCode(code);

        ImportDeclaration imp = (ImportDeclaration)cu.getChildNodes().get(0);
        assertEquals("import static com.github.javaparser.ParseStart.*;", lpp.print(imp));
    }

}
