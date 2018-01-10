package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.logic.ObjectProvider;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

/**
 * @author Federico Tomassetti
 */
public class MyObjectProvider implements ObjectProvider {

    public static final MyObjectProvider INSTANCE = new MyObjectProvider();

    private MyObjectProvider() {
        // prevent instantiation
    }

    @Override
    public ResolvedReferenceType object() {
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, new ReflectionTypeSolver()), new ReflectionTypeSolver());
    }

    @Override
    public ResolvedReferenceType byName(String qualifiedName) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(qualifiedName);
        if (!typeDeclaration.getTypeParameters().isEmpty()) {
            throw new UnsupportedOperationException();
        }
        return new ReferenceTypeImpl(typeDeclaration, typeSolver);
    }

}
