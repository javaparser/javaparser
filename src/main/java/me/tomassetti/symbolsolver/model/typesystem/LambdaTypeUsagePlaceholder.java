package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.List;

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
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
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

}
