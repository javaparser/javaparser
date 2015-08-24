package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 21/08/15.
 */
public class ArrayTypeUsage implements TypeUsage {
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ArrayTypeUsage that = (ArrayTypeUsage) o;

        if (!baseType.equals(that.baseType)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return baseType.hashCode();
    }

    private TypeUsage baseType;

    public ArrayTypeUsage(TypeUsage baseType) {
        this.baseType = baseType;
    }

    @Override
    public boolean isArray() {
        return true;
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        return Optional.empty();
    }

    @Override
    public String getTypeName() {
        return baseType.getTypeName()+"[]";
    }

    @Override
    public TypeUsage getBaseType() {
        return baseType;
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
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        if (other instanceof ArrayTypeUsage) {
            return baseType.isAssignableBy(((ArrayTypeUsage) other).baseType, typeSolver);
        } else {
            return false;
        }
    }

    @Override
    public String getQualifiedName() {
        return baseType.getQualifiedName() + "[]";
    }

    @Override
    public String prettyPrint() {
        return baseType.prettyPrint()+"[]";
    }
}
