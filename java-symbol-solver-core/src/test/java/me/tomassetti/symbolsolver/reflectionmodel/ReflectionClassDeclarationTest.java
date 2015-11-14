package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

public class ReflectionClassDeclarationTest {

    @Test
    public void testIsClass() {
        class Foo<E> { E field; }
        class Bar extends Foo<String> { }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

    @Test
    public void testGetSuperclassSimpleImplicit() {
        class Foo<E> { E field; }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals(Object.class.getCanonicalName(), foo.getSuperClass().getQualifiedName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().parameters());
    }

    @Test
    public void testGetSuperclassSimple() {
        class Bar { }
        class Foo<E> extends Bar  { E field; }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals("Bar", foo.getSuperClass().getTypeDeclaration().getName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().parameters());
    }

    @Test
    public void testGetSuperclassWithGenericSimple() {
        class Foo<E> { E field; }
        class Bar extends Foo<String> { }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().parameters().size());
        assertEquals(String.class.getCanonicalName(), bar.getSuperClass().parameters().get(0).asReferenceTypeUsage().getQualifiedName());
    }

    @Test
    public void testGetSuperclassWithGenericInheritanceSameName() {
        class Foo<E> { E field; }
        class Bar<E> extends Foo<E> { }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().parameters().size());
        assertEquals(true, bar.getSuperClass().parameters().get(0).isTypeVariable());
        assertEquals("E", bar.getSuperClass().parameters().get(0).asTypeParameter().getName());
        assertEquals(true, bar.getSuperClass().parameters().get(0).asTypeParameter().declaredOnClass());
        assertEquals(false, bar.getSuperClass().parameters().get(0).asTypeParameter().declaredOnMethod());
        assertTrue(bar.getSuperClass().parameters().get(0).asTypeParameter().getQNameOfDeclaringClass().endsWith("Bar"));
    }

    @Test
    public void testGetSuperclassWithGenericInheritanceDifferentName() {
        class Foo<E> { E field; }
        class Bar extends Foo<String> { }

        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

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
