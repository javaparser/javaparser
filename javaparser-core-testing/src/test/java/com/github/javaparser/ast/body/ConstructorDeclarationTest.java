package com.github.javaparser.ast.body;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ConstructorDeclarationTest {
    @Test
    void acceptsSuper() {
        ConstructorDeclaration cons = new ConstructorDeclaration("Cons");
        cons.createBody().addStatement("super();");

        assertEquals(String.format("public Cons() {%1$s" +
                "    super();%1$s" +
                "}", EOL), cons.toString());
    }
}
