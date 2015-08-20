package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 18/08/15.
 */
public class PrimitiveTypeUsage implements TypeUsage {

    private String name;

    public static final PrimitiveTypeUsage INT = new PrimitiveTypeUsage("int");
    public static final PrimitiveTypeUsage BOOLEAN = new PrimitiveTypeUsage("boolean");

    private PrimitiveTypeUsage(String name) {
        this.name = name;
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return true;
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        return Optional.empty();
    }

    @Override
    public boolean isFunctionOrPredicate() {
        return false;
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String getTypeName() {
        return name;
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
    public boolean isTypeVariable() {
        return false;
    }
}
