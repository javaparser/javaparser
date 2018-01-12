package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * @author Federico Tomassetti
 */
public class JavaParserAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private com.github.javaparser.ast.body.AnnotationMemberDeclaration wrappedNode;
    private TypeSolver typeSolver;

    public AnnotationMemberDeclaration getWrappedNode() {
        return wrappedNode;
    }

    public JavaParserAnnotationMemberDeclaration(AnnotationMemberDeclaration wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ResolvedType getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return wrappedNode.getNameAsString();
    }
}
