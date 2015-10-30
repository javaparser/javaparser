package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;

public class VoidTypeUsage implements TypeUsage {
    public static final TypeUsage INSTANCE = new VoidTypeUsage();

    private VoidTypeUsage() {
    }

    @Override
    public String describe() {
        return "void";
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        throw new UnsupportedOperationException();
    }
}
