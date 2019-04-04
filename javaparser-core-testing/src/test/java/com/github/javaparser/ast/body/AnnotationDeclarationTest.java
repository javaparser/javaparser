package com.github.javaparser.ast.body;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class AnnotationDeclarationTest {
    @Test
    void cantAddField() {
        assertThrows(IllegalStateException.class, () -> new AnnotationDeclaration().addField(Object.class, "oo"));
    }
}