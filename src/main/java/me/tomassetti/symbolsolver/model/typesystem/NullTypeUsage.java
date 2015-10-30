package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;

/**
 * This is a virtual type used to represent null values.
 */
public class NullTypeUsage implements TypeUsage {

    public static final NullTypeUsage INSTANCE = new NullTypeUsage();

    private NullTypeUsage() {

    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    public boolean isNull() {
        return true;
    }

    @Override
    public boolean isReferenceType() {
        return true;
    }

    @Override
    public String describe() {
        return "null";
    }

    @Override
    public List<TypeUsage> parameters() {
        return Collections.emptyList();
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

}
