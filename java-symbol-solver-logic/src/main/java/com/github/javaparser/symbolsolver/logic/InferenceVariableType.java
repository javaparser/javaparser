package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.Wildcard;

import java.util.HashSet;
import java.util.Set;

/**
 * An element using during type inference.
 *
 * @author Federico Tomassetti
 */
public class InferenceVariableType implements Type {

    private static int nextId = 0;

    private int id;
    private Set<Type> equivalentTypes = new HashSet<>();
    private Set<Type> superTypes = new HashSet<>();

    public InferenceVariableType() {
        this.id = nextId++;
    }

    public static InferenceVariableType fromWildcard(Wildcard wildcard) {
        InferenceVariableType inferenceVariableType = new InferenceVariableType();
        if (wildcard.isExtends()) {
            inferenceVariableType.superTypes.add(wildcard.getBoundedType());
        }
        if (wildcard.isSuper()) {
            // I am not sure about this one...
            inferenceVariableType.superTypes.add(wildcard.getBoundedType());
        }
        return inferenceVariableType;
    }

    @Override
    public String describe() {
        return "InferenceVariable_" + id;
    }

    @Override
    public boolean isAssignableBy(Type other) {
        throw new UnsupportedOperationException();
    }
}
