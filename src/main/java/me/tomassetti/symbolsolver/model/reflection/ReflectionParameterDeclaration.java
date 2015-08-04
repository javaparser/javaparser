package me.tomassetti.symbolsolver.model.reflection;

import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionParameterDeclaration implements ParameterDeclaration {
    private Class<?> type;

    public ReflectionParameterDeclaration(Class<?> type) {
        this.type = type;
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return true;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        return new ReflectionClassDeclaration(type);
    }
}
