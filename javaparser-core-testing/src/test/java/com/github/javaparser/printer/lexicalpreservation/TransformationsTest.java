package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static com.github.javaparser.ast.Modifier.Keyword.STATIC;

/**
 * These tests are more "high level" than the ones in LexicalPreservingPrinterTest.
 * The idea is to perform some transformations on the code, print it back and see if the generated code
 * is the expected one. We do not care about the internal state of LexicalPreservingPrinter, just the visible result.
 */
class TransformationsTest extends  AbstractLexicalPreservingTest {

    @Test
    void unchangedSimpleClasses() throws IOException {
        assertUnchanged("Example1");
        assertUnchanged("Example2");
    }

    @Test
    void unchangedComplexFile() throws IOException {
        assertUnchanged("Example4");
    }

    @Test
    void example1() throws IOException {
        considerExample("Example1_original");
        cu.getClassByName("A").get().getFieldByName("a").get().setModifiers(STATIC);
        assertTransformed("Example1", cu);
    }

    @Test
    void example2() throws IOException {
        considerExample("Example2_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer("10");
        assertTransformed("Example2", cu);
    }

    @Test
    void example3() throws IOException {
        considerExample("Example3_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer((Expression) null);
        assertTransformed("Example3", cu);
    }

    @Test
    void example5() throws IOException {
        considerExample("Example5_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer(new NullLiteralExpr());
        assertTransformed("Example5", cu);
    }

    @Test
    void example6() throws IOException {
        considerExample("Example6_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setName("someOtherName");
        assertTransformed("Example6", cu);
    }

    @Test
    void example7() throws IOException {
        considerExample("Example7_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setType(new ArrayType(PrimitiveType.intType()));
        assertTransformed("Example7", cu);
    }

    @Test
    void example8() throws IOException {
        considerExample("Example8_original");
        FieldDeclaration fd = cu.getClassByName("A").get().getMember(0).asFieldDeclaration();
        fd.addVariable(new VariableDeclarator(PrimitiveType.intType(), "b"));
        assertTransformed("Example8", cu);
    }

    @Test
    void example9() throws IOException {
        considerExample("Example9_original");
        FieldDeclaration fd = cu.getClassByName("A").get().getMember(0).asFieldDeclaration();
        fd.addVariable(new VariableDeclarator(new ArrayType(PrimitiveType.intType()), "b"));
        assertTransformed("Example9", cu);
    }

    @Test
    void example10() throws IOException {
        considerExample("Example10_original");
        cu.getClassByName("A").get().getMembers().remove(0);
        assertTransformed("Example10", cu);
    }

    @Test
    void exampleParam1() throws IOException {
        considerExample("Example_param1_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.addParameter("int", "p1");
        assertTransformed("Example_param1", cu);
    }

    @Test
    void exampleParam2() throws IOException {
        considerExample("Example_param1_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.addParameter(new ArrayType(PrimitiveType.intType()), "p1");
        md.addParameter("char", "p2");
        assertTransformed("Example_param2", cu);
    }

    @Test
    void exampleParam3() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.getParameters().remove(0);
        assertTransformed("Example_param3", cu);
    }

    @Test
    void exampleParam4() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.getParameters().remove(1);
        assertTransformed("Example_param4", cu);
    }

    @Test
    void exampleParam5() throws IOException {
        considerExample("Example_param3_original");
        MethodDeclaration md = cu.getClassByName("A").get().getMember(0).asMethodDeclaration();
        md.setType(PrimitiveType.intType());
        assertTransformed("Example_param5b", cu);
        md.getBody().get().getStatements().add(new ReturnStmt(new NameExpr("p1")));
        assertTransformed("Example_param5", cu);
    }
}
