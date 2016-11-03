package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.symbolsolver.logic.ObjectProvider;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

/**
 * @author Federico Tomassetti
 */
public class MyObjectProvider implements ObjectProvider {

    public static final MyObjectProvider INSTANCE = new MyObjectProvider();

    private MyObjectProvider() {

    }

    @Override
    public ReferenceType object() {
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, new ReflectionTypeSolver()), new ReflectionTypeSolver());
    }
}
