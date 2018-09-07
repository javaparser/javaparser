package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Method;

/**
 * @author Malte Skoruppa
 */
public class ReflectionAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private Method annotationMember;
    private TypeSolver typeSolver;

    public ReflectionAnnotationMemberDeclaration(Method annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        throw new UnsupportedOperationException("Obtaining the default value of reflection annotation member is not supported yet.");
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
