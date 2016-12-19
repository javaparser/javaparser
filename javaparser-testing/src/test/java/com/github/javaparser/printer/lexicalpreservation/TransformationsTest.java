package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.expr.Expression;
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
        String expectedCode = readExample(exampleName + "_transformed");
        String actualCode = lpp.print(cu);
        assertEquals(expectedCode, actualCode);
    }

    private void assertUnchanged(String exampleName) throws IOException {
        String code = considerExample(exampleName + "_original");
        assertEquals(code, lpp.print(cu));
    }

    @Test
    public void unchanged() throws IOException {
        assertUnchanged("Example1");
        assertUnchanged("Example2");
    }

    @Test
    public void example1() throws IOException {
        considerExample("Example1_original");
        cu.getClassByName("A").getFieldByName("a").setModifiers(EnumSet.of(Modifier.STATIC));
        assertTransformed("Example1", cu);
    }

    @Test
    public void example2() throws IOException {
        considerExample("Example2_original");
        cu.getClassByName("A").getFieldByName("a").getVariable(0).setInitializer("10");
        assertTransformed("Example2", cu);
    }

    @Test
    public void example3() throws IOException {
        considerExample("Example3_original");
        cu.getClassByName("A").getFieldByName("a").getVariable(0).setInitializer((Expression) null);
        assertTransformed("Example3", cu);
    }

}
