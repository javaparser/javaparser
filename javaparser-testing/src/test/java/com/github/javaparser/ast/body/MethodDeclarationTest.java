package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import org.junit.Test;

import static com.github.javaparser.JavaParser.*;

public class MethodDeclarationTest {
    @Test
    public void annotationsAllowedAfterGenericsAndBeforeReturnType() {
        parseClassBodyDeclaration("public <T> @Abc String method() {return null;}");
    }

    @Test
    public void annotationsAllowedBeforeGenerics() {
        parseClassBodyDeclaration("public @Abc <T> String method() {return null;}");
    }
    
    @Test
    public void explicitReceiverParameters() {
//        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void InnerInner(@mypackage.Anno Source.@mypackage.Anno Inner Source.Inner.this) { }");
//        assertEquals(true, method.getParameter(0).isExplicitReceiverParameter());
    }
}
