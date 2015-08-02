package me.tomassetti.symbolsolver.model.javaparser.declarations;

import me.tomassetti.symbolsolver.model.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.TypeDeclaration;

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
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }
}
