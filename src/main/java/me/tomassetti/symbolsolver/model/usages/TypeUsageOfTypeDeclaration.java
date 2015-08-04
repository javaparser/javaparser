package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 31/07/15.
 */
public class TypeUsageOfTypeDeclaration implements TypeUsage {

    private TypeDeclaration typeDeclaration;
    private List<TypeUsage> typeParameters;

    public TypeUsageOfTypeDeclaration(TypeDeclaration typeDeclaration) {
        this(typeDeclaration, Collections.emptyList());
    }

    public TypeUsageOfTypeDeclaration(TypeDeclaration typeDeclaration, List<TypeUsage> typeParameters) {
        this.typeDeclaration = typeDeclaration;
        this.typeParameters = typeParameters;
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
    public String toString() {
        return "TypeUsageOfTypeDeclaration{" +
                "typeDeclaration=" + typeDeclaration +
                '}';
    }

    @Override
    public String getTypeName() {
        return typeDeclaration.getQualifiedName();
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

    @Override
    public List<TypeUsage> parameters() {
        return typeParameters;
    }

    public boolean isFunctionOrPredicate() {
        return false;
    }
}
