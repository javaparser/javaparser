package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.Collections;
import java.util.List;

/**
 * Created by federico on 17/08/15.
 */
public class VoidTypeDeclaration implements TypeDeclaration {
    @Override
    public String getQualifiedName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        throw new UnsupportedOperationException();
    }

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
    public List<TypeParameter> getTypeParameters() {
        return Collections.emptyList();
    }
}
