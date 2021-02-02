package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserTypeVariableDeclarationTest {

    private JavaParserTypeVariableDeclaration createValue() {
        TypeParameter typeParameter = new TypeParameter();
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserTypeVariableDeclaration(typeParameter, typeSolver);
    }

    @Test
    void isTypeShouldBeTrue() {
        assertTrue(createValue().isType());
    }

    @Test
    void isTypeParameterShouldBeTrue() {
        assertTrue(createValue().isTypeParameter());
    }

    @Test
    void isParameterShouldBeFalse() {
        assertFalse(createValue().isParameter());
    }

    @Test
    void isFieldShouldBeFalse() {
        assertFalse(createValue().isField());
    }

    @Test
    void isClassShouldBeFalse() {
        assertFalse(createValue().isClass());
    }

    @Test
    void isInterfaceShouldBeFalse() {
        assertFalse(createValue().isInterface());
    }

}