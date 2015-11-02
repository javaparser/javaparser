package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import static org.junit.Assert.*;

public class ReflectionClassDeclarationTest {

    @Test
    public void testGetFieldDeclarationTypeVariableInheritance() {
        class Foo<E> { E field; }
        class Bar extends Foo<String> { }

        TypeSolver typeResolver = new JreTypeSolver();

        TypeDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        TypeDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        FieldDeclaration fooField = foo.getField("field");
        assertEquals(true, fooField.getType().isTypeVariable());
        assertEquals("E", fooField.getType().asTypeParameter().getName());

        FieldDeclaration barField = bar.getField("field");
        assertEquals(true, barField.getType().isReferenceType());
        assertEquals(String.class.getCanonicalName(), barField.getType().asReferenceTypeUsage().getQualifiedName());
    }

}
