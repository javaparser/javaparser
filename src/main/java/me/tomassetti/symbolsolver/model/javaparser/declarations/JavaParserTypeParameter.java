package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import me.tomassetti.symbolsolver.model.TypeParameter;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserTypeParameter implements TypeParameter {

    private com.github.javaparser.ast.TypeParameter wrappedNode;

    public JavaParserTypeParameter(com.github.javaparser.ast.TypeParameter wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean declaredOnClass() {
        return (wrappedNode.getParentNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Override
    public boolean declaredOnMethod() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }
}
