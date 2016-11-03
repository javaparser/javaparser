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
    @Override
    public String toString() {
        return "InferenceVariableType{" +
                "id=" + id +
                '}';
    }

    private int id;
    private Set<Type> equivalentTypes = new HashSet<>();

    public void registerEquivalentType(Type type) {
        this.equivalentTypes.add(type);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof InferenceVariableType)) return false;

        InferenceVariableType that = (InferenceVariableType) o;

        return id == that.id;

    }

    @Override
    public int hashCode() {
        return id;
    }

    private Set<Type> superTypes = new HashSet<>();

    public InferenceVariableType(int id) {
        this.id = id;
    }

    public static InferenceVariableType fromWildcard(Wildcard wildcard, int id) {
        InferenceVariableType inferenceVariableType = new InferenceVariableType(id);
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

    public Type equivalentType() {
        if (equivalentTypes.size() == 1) {
            return equivalentTypes.iterator().next();
        } else {
            throw new IllegalStateException();
        }
    }
}
