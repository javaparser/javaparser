package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class CompilationUnitTest {
    @Test
    public void issue578TheFirstCommentIsWithinTheCompilationUnit() {
        CompilationUnit compilationUnit = JavaParser.parse("// This is my class, with my comment\n" +
                "class A {\n" +
                "    static int a;\n" +
                "}");

        assertEquals(1, compilationUnit.getAllContainedComments().size());
    }
}
