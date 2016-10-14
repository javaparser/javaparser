package me.tomassetti.symbolsolver.javaparsermodel;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

/**
 * Placeholder used to represent a lambda argument type while it is being
 * calculated.
 */
public class LambdaArgumentTypePlaceholder implements Type {

    private int pos;
    private SymbolReference<MethodDeclaration> method;

    public LambdaArgumentTypePlaceholder(int pos) {
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
    public boolean isAssignableBy(Type other) {
        throw new UnsupportedOperationException();
    }
}
