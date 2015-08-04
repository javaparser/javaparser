package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;

/**
 * Created by federico on 02/08/15.
 */
public class LambdaTypeUsagePlaceholder implements TypeUsage {
    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public boolean isFunctionOrPredicate() {
        return true;
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String getTypeName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeUsage getBaseType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeUsage> parameters() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }
}
