package com.github.javaparser.ast.resolution.logic;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.resolution.TypeSolver;

public class FindMostApplicableTest extends MethodResolutionLogic {
    @Test
    public void testApplicableMethodsEmpty() {
        List<ResolvedMethodDeclaration> candidateSolvedMethods = new ArrayList<>();
        List<ResolvedType> argumentsTypes = new ArrayList<>();
        TypeSolver typeSolver = new ReflectionTypeSolver();

        SymbolReference<ResolvedMethodDeclaration> applicableMethods = findMostApplicable(candidateSolvedMethods, "",
                argumentsTypes, typeSolver);

        assertEquals(SymbolReference.unsolved(), applicableMethods);
    }
}
