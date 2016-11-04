package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;
import com.github.javaparser.symbolsolver.model.typesystem.Wildcard;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

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
    private TypeParameterDeclaration correspondingTp;

    public void setCorrespondingTp(TypeParameterDeclaration correspondingTp) {
        this.correspondingTp = correspondingTp;
    }

    private Set<Type> equivalentTypes = new HashSet<>();
    private ObjectProvider objectProvider;

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

    public InferenceVariableType(int id, ObjectProvider objectProvider) {
        this.id = id;
        this.objectProvider = objectProvider;
    }

    public static InferenceVariableType fromWildcard(Wildcard wildcard, int id, ObjectProvider objectProvider) {
        InferenceVariableType inferenceVariableType = new InferenceVariableType(id, objectProvider);
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

    private Set<Type> concreteEquivalentTypesAlsoIndirectly(Set<InferenceVariableType> considered, InferenceVariableType inferenceVariableType) {
        considered.add(inferenceVariableType);
        Set<Type> result = new HashSet<>();
        result.addAll(inferenceVariableType.equivalentTypes.stream().filter(t -> !t.isTypeVariable() && !(t instanceof InferenceVariableType)).collect(Collectors.toSet()));
        inferenceVariableType.equivalentTypes.stream().filter(t -> t instanceof InferenceVariableType).forEach(t -> {
            InferenceVariableType ivt = (InferenceVariableType)t;
            if (!considered.contains(ivt)) {
                result.addAll(concreteEquivalentTypesAlsoIndirectly(considered, ivt));
            }
        });
        return result;
    }

    public Type equivalentType() {
        Set<Type> concreteEquivalent = concreteEquivalentTypesAlsoIndirectly(new HashSet<>(), this);
        if (concreteEquivalent.isEmpty()) {
            if (correspondingTp == null) {
                return objectProvider.object();
            } else {
                return new TypeVariable(correspondingTp);
            }
        }
        if (concreteEquivalent.size() == 1) {
            return concreteEquivalent.iterator().next();
        }
        Set<Type> notTypeVariables = equivalentTypes.stream().filter(t -> !t.isTypeVariable()).collect(Collectors.toSet());
        if (notTypeVariables.size() == 1) {
            return notTypeVariables.iterator().next();
        } else if (notTypeVariables.size() == 0 && !superTypes.isEmpty()) {
            if (superTypes.size() == 1) {
                return superTypes.iterator().next();
            } else {
                throw new IllegalStateException("Super types are: " + superTypes);
            }
        } else {
            throw new IllegalStateException("Equivalent types are: " + equivalentTypes);
        }
    }
}
