package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.HashSet;
import java.util.Set;

public abstract class AbstractTypeDeclaration implements TypeDeclaration {

    protected abstract TypeSolver typeSolver();

    @Override
    public Set<MethodUsage> getAllMethods() {
        Set<MethodUsage> methods = new HashSet<>();

        for (MethodDeclaration methodDeclaration : getDeclaredMethods()) {
            methods.add(new MethodUsage(methodDeclaration, typeSolver()));
        }

        for (ReferenceTypeUsage ancestor : getAllAncestors()) {
            methods.addAll(ancestor.getDeclaredMethods());
        }

        return methods;
    }

}
