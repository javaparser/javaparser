package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.io.IOException;
import java.util.EnumSet;

import static org.junit.Assert.assertEquals;

/**
 * These tests are more "high level" than the ones in LexicalPreservingPrinterTest.
 * The idea is to perform some transformations on the code, print it back and see if the generated code
 * is the expected one. We do not care about the internal state of LexicalPreservingPrinter, just the visible result.
 */
public class TransformationsTest extends  AbstractLexicalPreservingTest {

    private void assertTransformed(String exampleName, CompilationUnit cu) throws IOException {
        String expectedCode = readExample(exampleName + "_expected");
        String actualCode = lpp.print(cu);
        assertEquals(expectedCode, actualCode);
    }

    private void assertUnchanged(String exampleName) throws IOException {
        String code = considerExample(exampleName + "_original");
        assertEquals(code, lpp.print(cu));
    }

    @Test
    public void unchangedSimpleClasses() throws IOException {
        assertUnchanged("Example1");
        assertUnchanged("Example2");
    }

    @Test
    public void unchangedComplexFile() throws IOException {
        assertUnchanged("Example4");
    }

    @Test
    public void example1() throws IOException {
        considerExample("Example1_original");
        cu.getClassByName("A").get().getFieldByName("a").get().setModifiers(EnumSet.of(Modifier.STATIC));
        assertTransformed("Example1", cu);
    }

    @Test
    public void example2() throws IOException {
        considerExample("Example2_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer("10");
        assertTransformed("Example2", cu);
    }

    @Test
    public void example3() throws IOException {
        considerExample("Example3_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer((Expression) null);
        assertTransformed("Example3", cu);
    }

    @Test
    public void example5() throws IOException {
        considerExample("Example5_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setInitializer(new NullLiteralExpr());
        assertTransformed("Example5", cu);
    }

    @Test
    public void example6() throws IOException {
        considerExample("Example6_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setName("someOtherName");
        assertTransformed("Example6", cu);
    }

    @Test
    public void example7() throws IOException {
        considerExample("Example7_original");
        cu.getClassByName("A").get().getFieldByName("a").get().getVariable(0).setType(new ArrayType(PrimitiveType.intType()));
        assertTransformed("Example7", cu);
    }

    @Test
    public void example8() throws IOException {
        considerExample("Example8_original");
        FieldDeclaration fd = (FieldDeclaration) cu.getClassByName("A").get().getMember(0);
        fd.addVariable(new VariableDeclarator(PrimitiveType.intType(), "b"));
        assertTransformed("Example8", cu);
    }

    @Test
    public void example9() throws IOException {
        considerExample("Example9_original");
        FieldDeclaration fd = (FieldDeclaration) cu.getClassByName("A").get().getMember(0);
        fd.addVariable(new VariableDeclarator(new ArrayType(PrimitiveType.intType()), "b"));
        assertTransformed("Example9", cu);
    }
}
