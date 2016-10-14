package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class ReflectionInterfaceDeclarationTest {

    @Test
    public void testGetDeclaredMethods() {
        TypeSolver typeResolver = new JreTypeSolver();
        TypeDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        List<MethodDeclaration> methods = list.getDeclaredMethods().stream()
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        assertEquals(28, methods.size());
        assertEquals("clear", methods.get(4).getName());
        assertEquals(true, methods.get(4).isAbstract());
        assertEquals(0, methods.get(4).getNoParams());
        assertEquals("contains", methods.get(5).getName());
        assertEquals(true, methods.get(5).isAbstract());
        assertEquals(1, methods.get(5).getNoParams());
        assertEquals(true, methods.get(5).getParam(0).getType().isReferenceType());
        assertEquals(Object.class.getCanonicalName(), methods.get(5).getParam(0).getType().asReferenceType().getQualifiedName());
    }

}
