package me.tomassetti.symbolsolver.resolution.javaparser;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

/**
 * Placeholder used to represent a lambda argument type while it is being
 * calculated.
 */
public class LambdaArgumentTypeUsagePlaceholder implements TypeUsage {

    private int pos;
    private SymbolReference<MethodDeclaration> method;

    public LambdaArgumentTypeUsagePlaceholder(int pos) {
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
    public boolean isAssignableBy(TypeUsage other) {
        throw new UnsupportedOperationException();
    }
}
