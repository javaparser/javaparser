package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.InterfaceDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

public class ReflectionMethodDeclarationTest {

    @Test
    public void testGetSignature() {
        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration object = new ReflectionClassDeclaration(Object.class, typeResolver);
        InterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);

        MethodDeclaration hashCode = object.getAllMethods().stream().filter(m -> m.getName().equals("hashCode")).findFirst().get().getDeclaration();
        MethodDeclaration equals = object.getAllMethods().stream().filter(m -> m.getName().equals("equals")).findFirst().get().getDeclaration();
        MethodDeclaration containsAll = list.getAllMethods().stream().filter(m -> m.getName().equals("containsAll")).findFirst().get().getDeclaration();
        MethodDeclaration subList = list.getAllMethods().stream().filter(m -> m.getName().equals("subList")).findFirst().get().getDeclaration();

        assertEquals("hashCode()", hashCode.getSignature());
        assertEquals("equals(java.lang.Object)", equals.getSignature());
        assertEquals("containsAll(java.util.Collection<? extends java.lang.Object>)", containsAll.getSignature());
        assertEquals("subList(int, int)", subList.getSignature());
    }
}
