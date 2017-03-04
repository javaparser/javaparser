package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import org.junit.Test;

public class MethodDeclarationTest {
    @Test
    public void annotationsAllowedAfterGenericsAndBeforeReturnType() {
        JavaParser.parseClassBodyDeclaration("public <T> @Abc String method() {return null;}");
    }

    @Test
    public void annotationsAllowedBeforeGenerics() {
        JavaParser.parseClassBodyDeclaration("public @Abc <T> String method() {return null;}");
    }
}
