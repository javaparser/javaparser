package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.CLASS_BODY;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class ConstructorDeclarationTest {
    private final JavaParser javaParser = new JavaParser();

    @Test
    public void acceptsSuper() {
        ConstructorDeclaration cons = new ConstructorDeclaration("Cons");
        cons.createBody().addStatement("super();");

        assertEquals(String.format("public Cons() {%1$s" +
                "    super();%1$s" +
                "}", EOL), cons.toString());
    }
    
    @Test
    public void receiverParametersNotAllowed() {
        ParseResult<BodyDeclaration<?>> result = javaParser.parse(CLASS_BODY, provider("X(X this, int y) { }"));
        assertProblems(result, "(line 1,col 20) The receiver cannot be used in a static context.");
    }

}
