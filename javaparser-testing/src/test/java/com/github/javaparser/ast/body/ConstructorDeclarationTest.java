package com.github.javaparser.ast.body;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ConstructorDeclarationTest {
    @Test
    public void acceptsSuper() {
        ConstructorDeclaration cons = new ConstructorDeclaration("Cons");
        cons.createBody().addStatement("super();");

        assertEquals("public Cons() {\n" +
                "    super();\n" +
                "}", cons.toString());
    }
}
