package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import org.junit.Test;

import static com.github.javaparser.ParseStart.CLASS_BODY;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class ConstructorDeclarationTest {
    @Test
    public void acceptsSuper() {
        ConstructorDeclaration cons = new ConstructorDeclaration("Cons");
        cons.createBody().addStatement("super();");

        assertEquals(String.format("public Cons() {%1$s" +
                "    super();%1$s" +
                "}", EOL), cons.toString());
    }
}
