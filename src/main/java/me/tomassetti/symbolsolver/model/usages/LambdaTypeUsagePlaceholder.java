package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 02/08/15.
 */
public class LambdaTypeUsagePlaceholder implements TypeUsage {

    private int pos;
    private SymbolReference<MethodDeclaration> method;

    public LambdaTypeUsagePlaceholder(int pos) {
        this.pos = pos;
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        throw new UnsupportedOperationException();
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

    public void setMethod(SymbolReference<MethodDeclaration> method) {
        this.method = method;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String prettyPrint() {
        throw new UnsupportedOperationException();
    }
}
