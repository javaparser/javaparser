package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;

import java.util.List;

/**
 * Created by federico on 17/08/15.
 */
public class JavaParserMethodDeclaration implements MethodDeclaration {

    private com.github.javaparser.ast.body.MethodDeclaration wrappedNode;

    public JavaParserMethodDeclaration(com.github.javaparser.ast.body.MethodDeclaration wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public TypeDeclaration declaringType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getReturnType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int getNoParams() {
        if (wrappedNode.getParameters() == null) {
            return 0;
        }
        return wrappedNode.getParameters().size();
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        return new JavaParserParameterDeclaration(wrappedNode.getParameters().get(i));
    }

    @Override
    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context) {
        throw new UnsupportedOperationException();
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
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}
