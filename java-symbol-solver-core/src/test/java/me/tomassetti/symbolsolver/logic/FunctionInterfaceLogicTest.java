package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.function.Consumer;
import java.util.function.Function;

import static org.junit.Assert.*;

public class FunctionInterfaceLogicTest {

    @Test
    public void testGetFunctionalMethodNegativeCaseOnClass() {
        TypeSolver typeSolver = new JreTypeSolver();
        TypeUsage string = new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        assertEquals(false, FunctionalInterfaceLogic.getFunctionalMethod(string).isPresent());
    }

    @Test
    public void testGetFunctionalMethodPositiveCasesOnInterfaces() {
        TypeSolver typeSolver = new JreTypeSolver();
        TypeUsage function = new ReferenceTypeUsageImpl(new ReflectionInterfaceDeclaration(Function.class, typeSolver), typeSolver);
        assertEquals(true, FunctionalInterfaceLogic.getFunctionalMethod(function).isPresent());
        assertEquals("apply", FunctionalInterfaceLogic.getFunctionalMethod(function).get().getName());
        TypeUsage consumer = new ReferenceTypeUsageImpl(new ReflectionInterfaceDeclaration(Consumer.class, typeSolver), typeSolver);
        assertEquals(true, FunctionalInterfaceLogic.getFunctionalMethod(consumer).isPresent());
        assertEquals("accept", FunctionalInterfaceLogic.getFunctionalMethod(consumer).get().getName());
    }
}
