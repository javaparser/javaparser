package me.tomassetti.symbolsolver.model.typesystem;

import com.github.javaparser.ast.type.WildcardType;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * Created by federico on 23/08/15.
 */
public class WildcardUsage implements TypeUsage {

    private WildcardType type;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        WildcardUsage that = (WildcardUsage) o;

        if (!type.equals(that.type)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return type.hashCode();
    }

    public WildcardUsage(WildcardType type) {
        if (type == null) {
            throw new NullPointerException();
        }
        this.type = type;
    }

    @Override
    public Optional<TypeUsage> parameterByName(String name) {
        return Optional.empty();
    }

    @Override
    public String getTypeName() {
        return type.toStringWithoutComments();
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
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQualifiedName() {
        return getTypeName();
    }

    @Override
    public String prettyPrint() {
        return getTypeName();
    }
}
