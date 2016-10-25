/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.Wildcard;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public final class TypeParametersLogic {

    private TypeParametersLogic() {
        // prevent instantiation
    }

    public static void determineTypeParameters(Map<TypeParameterDeclaration, Type> determinedTypeParameters, Type formalParamType, Type actualParamType, TypeSolver typeSolver) {
        if (actualParamType.isNull()) {
            return;
        }
        if (actualParamType.isTypeVariable()) {
            return;
        }
        if (formalParamType.isTypeVariable()) {
            determinedTypeParameters.put(formalParamType.asTypeParameter(), actualParamType);
            return;
        }
        if (formalParamType instanceof Wildcard) {
            return;
        }
        if (formalParamType.isArray() && actualParamType.isArray()) {
            determineTypeParameters(
                    determinedTypeParameters,
                    formalParamType.asArrayType().getComponentType(),
                    actualParamType.asArrayType().getComponentType(),
                    typeSolver);
            return;
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()
                && !formalParamType.asReferenceType().getQualifiedName().equals(actualParamType.asReferenceType().getQualifiedName())) {
            List<ReferenceType> ancestors = actualParamType.asReferenceType().getAllAncestors();
            final String formalParamTypeQName = formalParamType.asReferenceType().getQualifiedName();
            List<Type> correspondingFormalType = ancestors.stream().filter((a) -> a.getQualifiedName().equals(formalParamTypeQName)).collect(Collectors.toList());
            if (correspondingFormalType.isEmpty()) {
                throw new IllegalArgumentException();
            }
            actualParamType = correspondingFormalType.get(0);
        }
        if (formalParamType.isReferenceType() && actualParamType.isReferenceType()) {
            if (formalParamType.asReferenceType().isRawType() || actualParamType.asReferenceType().isRawType()) {
                return;
            }
            List<Type> formalTypeParams = formalParamType.asReferenceType().typeParametersValues();
            List<Type> actualTypeParams = actualParamType.asReferenceType().typeParametersValues();
            if (formalTypeParams.size() != actualTypeParams.size()) {
                throw new UnsupportedOperationException();
            }
            for (int i = 0; i < formalTypeParams.size(); i++) {
                determineTypeParameters(determinedTypeParameters, formalTypeParams.get(i), actualTypeParams.get(i), typeSolver);
            }
        }
    }
}
