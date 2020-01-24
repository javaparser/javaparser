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
import com.github.javaparser.resolution.types.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class InferenceContext {

    private int nextInferenceVariableId = 0;
    private ObjectProvider objectProvider;
    private List<InferenceVariableType> inferenceVariableTypes = new ArrayList<>();
    private Map<String, InferenceVariableType> inferenceVariableTypeMap = new HashMap<>();

    public InferenceContext(ObjectProvider objectProvider) {
        this.objectProvider = objectProvider;
    }

    private InferenceVariableType inferenceVariableTypeForTp(ResolvedTypeParameterDeclaration tp) {
        if (!inferenceVariableTypeMap.containsKey(tp.getName())) {
            InferenceVariableType inferenceVariableType = new InferenceVariableType(nextInferenceVariableId++, objectProvider);
            inferenceVariableTypes.add(inferenceVariableType);
            inferenceVariableType.setCorrespondingTp(tp);
            inferenceVariableTypeMap.put(tp.getName(), inferenceVariableType);
        }
        return inferenceVariableTypeMap.get(tp.getName());
    }

    /**
     * @return the actual with the inference variable inserted
     */
    public ResolvedType addPair(ResolvedType target, ResolvedType actual) {
        target = placeInferenceVariables(target);
        actual = placeInferenceVariables(actual);
        registerCorrespondance(target, actual);
        return target;
    }

    public ResolvedType addSingle(ResolvedType actual) {
        return placeInferenceVariables(actual);
    }

    private void registerCorrespondance(ResolvedType formalType, ResolvedType actualType) {
        if (formalType.isReferenceType() && actualType.isReferenceType()) {
            ResolvedReferenceType formalTypeAsReference = formalType.asReferenceType();
            ResolvedReferenceType actualTypeAsReference = actualType.asReferenceType();

            if (!formalTypeAsReference.getQualifiedName().equals(actualTypeAsReference.getQualifiedName())) {
                List<ResolvedReferenceType> ancestors = actualTypeAsReference.getAllAncestors();
                final String formalParamTypeQName = formalTypeAsReference.getQualifiedName();
                List<ResolvedType> correspondingFormalType = ancestors.stream().filter((a) -> a.getQualifiedName().equals(formalParamTypeQName)).collect(Collectors.toList());
                if (correspondingFormalType.isEmpty()) {
                    ancestors = formalTypeAsReference.getAllAncestors();
                    final String actualParamTypeQname = actualTypeAsReference.getQualifiedName();
                    List<ResolvedType> correspondingActualType = ancestors.stream().filter(a -> a.getQualifiedName().equals(actualParamTypeQname)).collect(Collectors.toList());
                    if (correspondingActualType.isEmpty()) {
                        throw new ConfilictingGenericTypesException(formalType, actualType);
                    }
                    correspondingFormalType = correspondingActualType;

                }
                actualTypeAsReference = correspondingFormalType.get(0).asReferenceType();
            }

            if (formalTypeAsReference.getQualifiedName().equals(actualTypeAsReference.getQualifiedName())) {
                if (!formalTypeAsReference.typeParametersValues().isEmpty()) {
                    if (actualTypeAsReference.isRawType()) {
                        // nothing to do
                    } else {
                        int i = 0;
                        for (ResolvedType formalTypeParameter : formalTypeAsReference.typeParametersValues()) {
                            registerCorrespondance(formalTypeParameter, actualTypeAsReference.typeParametersValues().get(i));
                            i++;
                        }
                    }
                }
            }
        } else if (formalType instanceof InferenceVariableType && !actualType.isPrimitive()) {
            ((InferenceVariableType) formalType).registerEquivalentType(actualType);
            if (actualType instanceof InferenceVariableType) {
                ((InferenceVariableType) actualType).registerEquivalentType(formalType);
            }
        } else if (actualType.isNull()) {
            // nothing to do
        } else if (actualType.equals(formalType)) {
            // nothing to do
        } else if (actualType.isArray() && formalType.isArray()) {
            registerCorrespondance(formalType.asArrayType().getComponentType(), actualType.asArrayType().getComponentType());
        } else if (formalType.isWildcard()) {
            // nothing to do
            if ((actualType instanceof InferenceVariableType) && formalType.asWildcard().isBounded()) {
                ((InferenceVariableType) actualType).registerEquivalentType(formalType.asWildcard().getBoundedType());
                if (formalType.asWildcard().getBoundedType() instanceof InferenceVariableType) {
                    ((InferenceVariableType) formalType.asWildcard().getBoundedType()).registerEquivalentType(actualType);
                }
            }
            if (actualType.isWildcard()) {
                ResolvedWildcard formalWildcard = formalType.asWildcard();
                ResolvedWildcard actualWildcard = actualType.asWildcard();
                if (formalWildcard.isBounded() && formalWildcard.getBoundedType() instanceof InferenceVariableType) {
                    if (formalWildcard.isSuper() && actualWildcard.isSuper()) {
                        ((InferenceVariableType) formalType.asWildcard().getBoundedType()).registerEquivalentType(actualWildcard.getBoundedType());
                    } else if (formalWildcard.isExtends() && actualWildcard.isExtends()) {
                        ((InferenceVariableType) formalType.asWildcard().getBoundedType()).registerEquivalentType(actualWildcard.getBoundedType());
                    }
                }
            }

            if (actualType.isReferenceType()) {
                if (formalType.asWildcard().isBounded()) {
                    registerCorrespondance(formalType.asWildcard().getBoundedType(), actualType);
                }
            }
        } else if (actualType instanceof InferenceVariableType) {
            if (formalType instanceof ResolvedReferenceType) {
                ((InferenceVariableType) actualType).registerEquivalentType(formalType);
            } else if (formalType instanceof InferenceVariableType) {
                ((InferenceVariableType) actualType).registerEquivalentType(formalType);
            }
        } else if (actualType.isConstraint()) {
            ResolvedLambdaConstraintType constraintType = actualType.asConstraintType();
            if (constraintType.getBound() instanceof InferenceVariableType) {
                ((InferenceVariableType) constraintType.getBound()).registerEquivalentType(formalType);
            }
        } else if (actualType.isPrimitive()) {
            if (formalType.isPrimitive()) {
                // nothing to do
            } else {
                registerCorrespondance(formalType, objectProvider.byName(actualType.asPrimitive().getBoxTypeQName()));
            }
        } else if (actualType.isReferenceType()) {
            if (formalType.isPrimitive()) {
                if (formalType.asPrimitive().getBoxTypeQName().equals(actualType.describe())) {
                    registerCorrespondance(objectProvider.byName(formalType.asPrimitive().getBoxTypeQName()), actualType);
                } else {
                    // nothing to do
                }
            } else {
                // nothing to do
            }
        } else {
            throw new UnsupportedOperationException(formalType.describe() + " " + actualType.describe());
        }
    }

    private ResolvedType placeInferenceVariables(ResolvedType type) {
        if (type.isWildcard()) {
            if (type.asWildcard().isExtends()) {
                return ResolvedWildcard.extendsBound(placeInferenceVariables(type.asWildcard().getBoundedType()));
            } else if (type.asWildcard().isSuper()) {
                return ResolvedWildcard.superBound(placeInferenceVariables(type.asWildcard().getBoundedType()));
            } else {
                return type;
            }
        } else if (type.isTypeVariable()) {
            return inferenceVariableTypeForTp(type.asTypeParameter());
        } else if (type.isReferenceType()) {
            return type.asReferenceType().transformTypeParameters(tp -> placeInferenceVariables(tp));
        } else if (type.isArray()) {
            return new ResolvedArrayType(placeInferenceVariables(type.asArrayType().getComponentType()));
        } else if (type.isNull() || type.isPrimitive() || type.isVoid()) {
            return type;
        } else if (type.isConstraint()) {
            return ResolvedLambdaConstraintType.bound(placeInferenceVariables(type.asConstraintType().getBound()));
        } else if (type instanceof InferenceVariableType) {
            return type;
        } else {
            throw new UnsupportedOperationException(type.describe());
        }
    }

    public ResolvedType resolve(ResolvedType type) {
        if (type instanceof InferenceVariableType) {
            InferenceVariableType inferenceVariableType = (InferenceVariableType) type;
            return inferenceVariableType.equivalentType();
        } else if (type.isReferenceType()) {
            return type.asReferenceType().transformTypeParameters(tp -> resolve(tp));
        } else if (type.isNull() || type.isPrimitive() || type.isVoid()) {
            return type;
        } else if (type.isArray()) {
            return new ResolvedArrayType(resolve(type.asArrayType().getComponentType()));
        } else if (type.isWildcard()) {
            if (type.asWildcard().isExtends()) {
                return ResolvedWildcard.extendsBound(resolve(type.asWildcard().getBoundedType()));
            } else if (type.asWildcard().isSuper()) {
                return ResolvedWildcard.superBound(resolve(type.asWildcard().getBoundedType()));
            } else {
                return type;
            }
        } else {
            throw new UnsupportedOperationException(type.describe());
        }
    }
}
