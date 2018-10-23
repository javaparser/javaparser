package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import javassist.CtMethod;

/**
 * @author Malte Skoruppa
 */
public class JavassistAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private CtMethod annotationMember;
    private TypeSolver typeSolver;

    public JavassistAnnotationMemberDeclaration(CtMethod annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        // TODO we should do something like this:
        // AnnotationDefaultAttribute defaultAttribute = (AnnotationDefaultAttribute) annotationMember.getMethodInfo().getAttribute(AnnotationDefaultAttribute.tag);
        // return defaultAttribute != null ? defaultAttribute.getDefaultValue() : null;
        // TODO ...but the interface wants us to return a JavaParser Expression node.
        throw new UnsupportedOperationException("Obtaining the default value of a library annotation member is not supported yet.");
    }

    @Override
    public ResolvedType getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }
}
