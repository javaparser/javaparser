package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class Substitution {

    private List<TypeParameterDeclaration> typeParameterDeclarations;
    private List<Type> types;

    private final static Substitution EMPTY = new Substitution();

    public static Substitution empty() {
        return EMPTY;
    }

    public Substitution withPair(TypeParameterDeclaration typeParameterDeclaration, Type type) {
        Substitution newInstance = new Substitution();
        newInstance.typeParameterDeclarations.addAll(this.typeParameterDeclarations);
        newInstance.types.addAll(this.types);
        newInstance.typeParameterDeclarations.add(typeParameterDeclaration);
        newInstance.types.add(type);
        return newInstance;

    }

    private Substitution() {
        this.typeParameterDeclarations = new LinkedList<>();
        this.types = new LinkedList<>();
    }

    public Type apply(Type originalType) {
        Type result = originalType;
        for (int i=0;i<typeParameterDeclarations.size();i++) {
            result = result.replaceTypeVariables(typeParameterDeclarations.get(i), types.get(i));
        }
        return result;
    }
}
