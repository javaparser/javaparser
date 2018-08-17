package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static org.junit.Assert.*;

public class TokenRangeTest {
    @Test
    public void toStringWorks() {
        CompilationUnit cu = JavaParser.parse("class X {\n\tX(){\n// hello\n}\n}");
        assertEquals("X(){\n// hello\n}", cu.getClassByName("X").get().getDefaultConstructor().get().getTokenRange().get().toString());
    }
}