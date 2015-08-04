package me.tomassetti.symbolsolver.model.javaparser.declarations;

import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * Created by federico on 02/08/15.
 */
public class JavaParserParameterDeclaration implements ParameterDeclaration {
    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }
}
