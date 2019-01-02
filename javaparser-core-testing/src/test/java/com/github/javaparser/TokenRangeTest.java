package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TokenRangeTest {
    @Test
    void toStringWorks() {
        CompilationUnit cu = JavaParser.parse("class X {\n\tX(){\n// hello\n}\n}");
        assertEquals("X(){\n// hello\n}", cu.getClassByName("X").get().getDefaultConstructor().get().getTokenRange().get().toString());
    }
}