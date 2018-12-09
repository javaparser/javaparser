package com.github.javaparser.ast.body;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parse;
import static org.junit.Assert.assertEquals;

public class FieldDeclarationTest {
    @Test
    public void wofjweoifj() {
        CompilationUnit compilationUnit = parse("" +
                "class A {\n" +
                "    int a, b;\n" +
                "}");

        BodyDeclaration<?> declaration = compilationUnit.getType(0).getMembers().get(0);
        FieldDeclaration fieldDeclaration = declaration.asFieldDeclaration();
        VariableDeclarator var1 = fieldDeclaration.getVariables().get(0);
        VariableDeclarator var2 = fieldDeclaration.getVariables().get(1);
        assertEquals(var1, var1.getType().getParentNode().get());
        assertEquals(var2, var2.getType().getParentNode().get());
    }
}
