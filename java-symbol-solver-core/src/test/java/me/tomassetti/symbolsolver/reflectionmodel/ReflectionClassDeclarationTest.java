package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.lang.reflect.Method;
import java.util.List;
import java.util.stream.Collectors;

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

    @Test
    public void testGetDeclaredMethods() {
        TypeSolver typeResolver = new JreTypeSolver();
        TypeDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        List<MethodDeclaration> methods = string.getDeclaredMethods().stream()
                .filter(m -> !m.isPrivate() && !m.isPackageProtected())
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        assertEquals(67, methods.size());
        assertEquals("charAt", methods.get(0).getName());
        assertEquals(false, methods.get(0).isAbstract());
        assertEquals(1, methods.get(0).getNoParams());
        assertEquals("int", methods.get(0).getParam(0).getType().describe());
        assertEquals("concat", methods.get(6).getName());
        assertEquals(false, methods.get(6).isAbstract());
        assertEquals(1, methods.get(6).getNoParams());
        assertEquals("java.lang.String", methods.get(6).getParam(0).getType().describe());
    }

}
