package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public abstract class AbstractTypeDeclaration implements TypeDeclaration {

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        return getContext().solveMethod(name, parameterTypes, typeSolver());
    }

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
