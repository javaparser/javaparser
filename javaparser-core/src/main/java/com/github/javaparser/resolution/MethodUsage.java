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

package com.github.javaparser.resolution;

import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametersMap;
import com.github.javaparser.resolution.types.parametrization.ResolvedTypeParametrized;


import java.util.*;

/**
 * This is basically a MethodDeclaration with some TypeParameters defined.
 * The defined TypeParameters can comes from the Method itself or from the surrounding types.
 *
 * @author Federico Tomassetti
 */
public class MethodUsage implements ResolvedTypeParametrized {
    private ResolvedMethodDeclaration declaration;
    private List<ResolvedType> paramTypes = new ArrayList<>();
    private List<ResolvedType> exceptionTypes = new ArrayList<>();
    private ResolvedType returnType;
    private ResolvedTypeParametersMap typeParametersMap;

    public MethodUsage(ResolvedMethodDeclaration declaration) {
        this.typeParametersMap = ResolvedTypeParametersMap.empty();
        this.declaration = declaration;
        for (int i = 0; i < declaration.getNumberOfParams(); i++) {
            paramTypes.add(declaration.getParam(i).getType());
        }
        for (int i = 0; i < declaration.getNumberOfSpecifiedExceptions(); i++) {
            exceptionTypes.add(declaration.getSpecifiedException(i));
        }
        returnType = declaration.getReturnType();
    }

    public MethodUsage(ResolvedMethodDeclaration declaration,
                       List<ResolvedType> paramTypes, ResolvedType returnType) {
        this(declaration, paramTypes, returnType, declaration.getSpecifiedExceptions(),
                ResolvedTypeParametersMap.empty());
    }

    public MethodUsage(ResolvedMethodDeclaration declaration, List<ResolvedType> paramTypes, ResolvedType returnType,
                       List<ResolvedType> exceptionTypes) {
        this(declaration, paramTypes, returnType, exceptionTypes, ResolvedTypeParametersMap.empty());
    }

    private MethodUsage(ResolvedMethodDeclaration declaration, List<ResolvedType> paramTypes, ResolvedType returnType,
                        List<ResolvedType> exceptionTypes, ResolvedTypeParametersMap typeParametersMap) {
        this.declaration = declaration;
        this.paramTypes = paramTypes;
        this.returnType = returnType;
        this.exceptionTypes = exceptionTypes;
        this.typeParametersMap = typeParametersMap;
    }

    @Override
    public String toString() {
        return "MethodUsage{" +
                "declaration=" + declaration +
                ", paramTypes=" + paramTypes +
                '}';
    }

    public ResolvedMethodDeclaration getDeclaration() {
        return declaration;
    }

    public String getName() {
        return declaration.getName();
    }

    public ResolvedReferenceTypeDeclaration declaringType() {
        return declaration.declaringType();
    }

    public ResolvedType returnType() {
        return returnType;
    }

    public List<ResolvedType> getParamTypes() {
        return paramTypes;
    }

    public MethodUsage replaceParamType(int i, ResolvedType replaced) {
        if (i < 0 || i >= getNoParams()) {
            throw new IllegalArgumentException();
        }
        if (paramTypes.get(i) == replaced) {
            return this;
        }
        List<ResolvedType> newParams = new LinkedList<>(paramTypes);
        newParams.set(i, replaced);
        return new MethodUsage(declaration, newParams, returnType, exceptionTypes, typeParametersMap);
    }

    public MethodUsage replaceExceptionType(int i, ResolvedType replaced) {
        if (i < 0 || i >= exceptionTypes.size()) {
            throw new IllegalArgumentException();
        }
        if (exceptionTypes.get(i) == replaced) {
            return this;
        }
        List<ResolvedType> newTypes = new LinkedList<>(exceptionTypes);
        newTypes.set(i, replaced);
        return new MethodUsage(declaration, paramTypes, returnType, newTypes, typeParametersMap);
    }

    public MethodUsage replaceReturnType(ResolvedType returnType) {
        if (returnType == this.returnType) {
            return this;
        } else {
            return new MethodUsage(declaration, paramTypes, returnType, exceptionTypes, typeParametersMap);
        }
    }

    /**
     * Return the number of formal arguments accepted by this method.
     */
    public int getNoParams() {
        return paramTypes.size();
    }

    /**
     * Return the type of the formal argument at the given position.
     */
    public ResolvedType getParamType(int i) {
        return paramTypes.get(i);
    }

    public MethodUsage replaceTypeParameter(ResolvedTypeParameterDeclaration typeParameter, ResolvedType type) {
        if (type == null) {
            throw new IllegalArgumentException();
        }

        // TODO if the method declaration has a type param with that name ignore this call
        MethodUsage res = new MethodUsage(declaration, paramTypes, returnType, exceptionTypes,
                typeParametersMap.toBuilder().setValue(typeParameter, type).build());

        Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes = new HashMap<>();
        for (int i = 0; i < paramTypes.size(); i++) {
            ResolvedType originalParamType = paramTypes.get(i);
            ResolvedType newParamType = originalParamType.replaceTypeVariables(typeParameter, type, inferredTypes);
            res = res.replaceParamType(i, newParamType);
        }
        for (int i = 0; i < exceptionTypes.size(); i++) {
            ResolvedType originalType = exceptionTypes.get(i);
            ResolvedType newType = originalType.replaceTypeVariables(typeParameter, type, inferredTypes);
            res = res.replaceExceptionType(i, newType);
        }
        ResolvedType oldReturnType = res.returnType;
        ResolvedType newReturnType = oldReturnType.replaceTypeVariables(typeParameter, type, inferredTypes);
        res = res.replaceReturnType(newReturnType);
        return res;
    }

    @Override
    public ResolvedTypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }

    public String getQualifiedSignature() {
        // TODO use the type parameters
        return this.getDeclaration().getQualifiedSignature();
    }

    public List<ResolvedType> exceptionTypes() {
        return exceptionTypes;
    }
}
