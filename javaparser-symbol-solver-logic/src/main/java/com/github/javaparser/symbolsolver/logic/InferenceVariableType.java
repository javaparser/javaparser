/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.ResolvedWildcard;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * An element using during type inference.
 *
 * @author Federico Tomassetti
 */
public class InferenceVariableType implements ResolvedType {
    @Override
    public String toString() {
        return "InferenceVariableType{" +
                "id=" + id +
                '}';
    }

    private int id;
    private ResolvedTypeParameterDeclaration correspondingTp;

    public void setCorrespondingTp(ResolvedTypeParameterDeclaration correspondingTp) {
        this.correspondingTp = correspondingTp;
    }

    private Set<ResolvedType> equivalentTypes = new HashSet<>();
    private ObjectProvider objectProvider;

    public void registerEquivalentType(ResolvedType type) {
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

    private Set<ResolvedType> superTypes = new HashSet<>();

    public InferenceVariableType(int id, ObjectProvider objectProvider) {
        this.id = id;
        this.objectProvider = objectProvider;
    }

    public static InferenceVariableType fromWildcard(ResolvedWildcard wildcard, int id, ObjectProvider objectProvider) {
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
    public boolean isAssignableBy(ResolvedType other) {
        throw new UnsupportedOperationException();
    }

    private Set<ResolvedType> concreteEquivalentTypesAlsoIndirectly(Set<InferenceVariableType> considered, InferenceVariableType inferenceVariableType) {
        considered.add(inferenceVariableType);
        Set<ResolvedType> result = new HashSet<>();
        result.addAll(inferenceVariableType.equivalentTypes.stream().filter(t -> !t.isTypeVariable() && !(t instanceof InferenceVariableType)).collect(Collectors.toSet()));
        inferenceVariableType.equivalentTypes.stream().filter(t -> t instanceof InferenceVariableType).forEach(t -> {
            InferenceVariableType ivt = (InferenceVariableType)t;
            if (!considered.contains(ivt)) {
                result.addAll(concreteEquivalentTypesAlsoIndirectly(considered, ivt));
            }
        });
        return result;
    }

    public ResolvedType equivalentType() {
        Set<ResolvedType> concreteEquivalent = concreteEquivalentTypesAlsoIndirectly(new HashSet<>(), this);
        if (concreteEquivalent.isEmpty()) {
            if (correspondingTp == null) {
                return objectProvider.object();
            } else {
                return new ResolvedTypeVariable(correspondingTp);
            }
        }
        if (concreteEquivalent.size() == 1) {
            return concreteEquivalent.iterator().next();
        }
        Set<ResolvedType> notTypeVariables = equivalentTypes.stream()
                                                    .filter(t -> !t.isTypeVariable() && !hasInferenceVariables(t))
                                                    .collect(Collectors.toSet());
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

    private boolean hasInferenceVariables(ResolvedType type){
        if (type instanceof InferenceVariableType){
            return true;
        }

        if (type.isReferenceType()){
            ResolvedReferenceType refType = type.asReferenceType();
            for (ResolvedType t : refType.typeParametersValues()){
                if (hasInferenceVariables(t)){
                    return true;
                }
            }
            return false;
        }

        if (type.isWildcard()){
            ResolvedWildcard wildcardType = type.asWildcard();
            return hasInferenceVariables(wildcardType.getBoundedType());
        }

        return false;
    }
}
