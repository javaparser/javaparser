package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.*;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.Type;
import org.junit.Test;

import java.util.Arrays;
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
        assertEquals(cu.getClassByName("A"), ((ChildTextElement)lpp.getTextForNode(cu).getTextElement(0)).getChild());

        // Class
        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
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

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
        FieldDeclaration fd = classA.getFieldByName("i");
        NodeText nodeText = lpp.getOrCreateNodeText(fd);
        assertEquals(Arrays.asList("int", " ", "i", ";"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethod() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        NodeText nodeText = lpp.getOrCreateNodeText(md);
        assertEquals(Arrays.asList("void", " ", "foo", "(", "int p1", ",", " ", "float p2", ")", " ", "{ }"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForMethodParameter() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParamByName("p1");
        NodeText nodeText = lpp.getOrCreateNodeText(p1);
        assertEquals(Arrays.asList("int", " ", "p1"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
    }

    @Test
    public void checkNodeTextCreatedForPrimitiveType() {
        String code = "class A {void foo(int p1, float p2) { }}";
        considerCode(code);

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
        MethodDeclaration md = classA.getMethodsByName("foo").get(0);
        Parameter p1 = md.getParamByName("p1");
        Type t = p1.getType();
        NodeText nodeText = lpp.getOrCreateNodeText(t);
        assertEquals(Arrays.asList("int"),
                nodeText.getElements().stream().map(TextElement::expand).collect(Collectors.toList()));
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

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A");
        classA.addField("int", "myField");
        assertEquals("class A {\n    int myField;\n}", lpp.print(classA));
    }

    @Test
    public void printASuperSimpleClassWithoutChanges() {
        String code = "class A {}";
        considerCode(code);

        assertEquals(code, lpp.print(cu.getClassByName("A")));
    }

    @Test
    public void printASimpleCUWithoutChanges() {
        String code = "class /*a comment*/ A {\t\t\n int f;\n\n\n         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        assertEquals(code, lpp.print(cu));
        assertEquals(code, lpp.print(cu.getClassByName("A")));
        assertEquals("void foo(int p  ) { return  'z'  \t; }", lpp.print(cu.getClassByName("A").getMethodsByName("foo").get(0)));
    }

    @Test
    public void printASimpleClassRemovingAField() {
        String code = "class /*a comment*/ A {\t\t\n int f;\n\n\n         void foo(int p  ) { return  'z'  \t; }}";
        considerCode(code);

        ClassOrInterfaceDeclaration c = cu.getClassByName("A");
        c.getMembers().remove(0);
        assertEquals("class /*a comment*/ A {\t\t\n" +
                " \n" +
                "\n" +
                "\n" +
                "         void foo(int p  ) { return  'z'  \t; }}", lpp.print(c));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithZeroParameters() {
        String code = "class A { void foo() {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
        m.addParameter("float", "p1");
        assertEquals("void foo(float p1) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodAddingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(char p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
        m.addParameter("float", "p2");
        assertEquals("void foo(char p1, float p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingAParameterToAMethodWithOneParameter() {
        String code = "class A { void foo(float p1) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo() {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterOneFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
        m.getParameters().remove(0);
        assertEquals("void foo(int p2) {}", lpp.print(m));
    }

    @Test
    public void printASimpleMethodRemovingParameterTwoFromMethodWithTwoParameters() {
        String code = "class A { void foo(char p1, int p2) {} }";
        considerCode(code);

        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
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
        NodeList<Statement> stmts = cu.getClassByName("A").getMethodsByName("foo").get(0).getBody().get().getStatements();
        stmts.add(s);
        MethodDeclaration m = cu.getClassByName("A").getMethodsByName("foo").get(0);
        assertEquals("void foo(char p1, int p2) {\n" +
                "    10 + 2;\n" +
                "}", lpp.print(m));
    }
}
