package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class TypeUsageOfTypeParameter implements TypeUsage {

    private TypeParameter typeParameter;

    @Override
    public String toString() {
        return "TypeUsageOfTypeParameter{" +
                "typeParameter=" + typeParameter +
                '}';
    }

    public TypeUsageOfTypeParameter(TypeParameter typeParameter) {
        this.typeParameter = typeParameter;
    }

    @Override
    public boolean isArray() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        return Optional.empty();
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        return Optional.empty();
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String getTypeName() {
        return typeParameter.getName();
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
        return Collections.emptyList();
    }

    @Override
    public TypeParameter asTypeParameter() {
        return typeParameter;
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        if (other.isTypeVariable()) {
            return getTypeName().equals(other.getTypeName());
        } else {
            return false;
        }
    }

    @Override
    public String getQualifiedName() {
        return getTypeName();
    }

    @Override
    public String prettyPrint() {
        return typeParameter.getName();
    }
}
