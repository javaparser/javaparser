package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;

public abstract class AbstractTypeDeclaration implements TypeDeclaration {

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        return getContext().solveMethod(name, parameterTypes, typeSolver());
    }

    protected abstract TypeSolver typeSolver();

}
