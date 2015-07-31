package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Created by federico on 31/07/15.
 */
public class TypeUsageOfTypeDeclaration implements TypeUsage {

    private TypeDeclaration typeDeclaration;

    public TypeUsageOfTypeDeclaration(TypeDeclaration typeDeclaration) {
        this.typeDeclaration = typeDeclaration;
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
        return true;
    }

    @Override
    public String getTypeName() {
        return typeDeclaration.getName();
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        return typeDeclaration.solveMethod(name, parameterTypes);
    }
}
