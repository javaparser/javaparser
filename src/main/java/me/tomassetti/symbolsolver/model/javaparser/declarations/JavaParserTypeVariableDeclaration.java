package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.TypeParameter;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserTypeVariableDeclaration implements TypeDeclaration {

    private TypeParameter wrappedNode;

    public JavaParserTypeVariableDeclaration(TypeParameter wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public String getQualifiedName() {
        return getName();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
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
        return true;
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
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
        return true;
    }

    @Override
    public List<me.tomassetti.symbolsolver.model.TypeParameter> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}
