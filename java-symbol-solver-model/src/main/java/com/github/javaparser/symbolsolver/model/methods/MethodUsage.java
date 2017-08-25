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

package com.github.javaparser.symbolsolver.model.methods;

import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.parametrization.TypeParametersMap;
import com.github.javaparser.symbolsolver.model.typesystem.parametrization.TypeParametrized;

import java.lang.ref.Reference;
import java.sql.Ref;
import java.util.*;

/**
 * This is basically a MethodDeclaration with some TypeParameters defined.
 * The defined TypeParameters can comes from the Method itself or from the surrounding types.
 *
 * @author Federico Tomassetti
 */
public class MethodUsage implements TypeParametrized {
    private MethodDeclaration declaration;
    private List<Type> paramTypes = new ArrayList<>();
    private List<Type> exceptionTypes = new ArrayList<>();
    private Type returnType;
    private TypeParametersMap typeParametersMap;

    public MethodUsage(MethodDeclaration declaration) {
        this.typeParametersMap = TypeParametersMap.empty();
        this.declaration = declaration;
        for (int i = 0; i < declaration.getNumberOfParams(); i++) {
            paramTypes.add(declaration.getParam(i).getType());
        }
        for (int i = 0; i < declaration.getNumberOfSpecifiedExceptions(); i++) {
            exceptionTypes.add(declaration.getSpecifiedException(i));
        }
        returnType = declaration.getReturnType();
    }

    public MethodUsage(MethodDeclaration declaration, List<Type> paramTypes, Type returnType) {
        this(declaration, paramTypes, returnType, declaration.getSpecifiedExceptions(), TypeParametersMap.empty());
    }

    public MethodUsage(MethodDeclaration declaration, List<Type> paramTypes, Type returnType,
                       List<Type> exceptionTypes) {
        this(declaration, paramTypes, returnType, exceptionTypes, TypeParametersMap.empty());
    }

    private MethodUsage(MethodDeclaration declaration, List<Type> paramTypes, Type returnType,
                        List<Type> exceptionTypes, TypeParametersMap typeParametersMap) {
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

    public MethodDeclaration getDeclaration() {
        return declaration;
    }

    public String getName() {
        return declaration.getName();
    }

    public ReferenceTypeDeclaration declaringType() {
        return declaration.declaringType();
    }

    public Type returnType() {
        return returnType;
    }

    public List<Type> getParamTypes() {
        return paramTypes;
    }

    public MethodUsage replaceParamType(int i, Type replaced) {
        if (i < 0 || i >= getNoParams()) {
            throw new IllegalArgumentException();
        }
        if (paramTypes.get(i) == replaced) {
            return this;
        }
        List<Type> newParams = new LinkedList<>(paramTypes);
        newParams.set(i, replaced);
        return new MethodUsage(declaration, newParams, returnType, exceptionTypes, typeParametersMap);
    }

    public MethodUsage replaceExceptionType(int i, Type replaced) {
        if (i < 0 || i >= exceptionTypes.size()) {
            throw new IllegalArgumentException();
        }
        if (exceptionTypes.get(i) == replaced) {
            return this;
        }
        List<Type> newTypes = new LinkedList<>(exceptionTypes);
        newTypes.set(i, replaced);
        return new MethodUsage(declaration, paramTypes, returnType, newTypes, typeParametersMap);
    }

    public MethodUsage replaceReturnType(Type returnType) {
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
    public Type getParamType(int i) {
        return paramTypes.get(i);
    }

    public MethodUsage replaceTypeParameter(TypeParameterDeclaration typeParameter, Type type) {
        if (type == null) {
            throw new IllegalArgumentException();
        }

        // TODO if the method declaration has a type param with that name ignore this call
        MethodUsage res = new MethodUsage(declaration, paramTypes, returnType, exceptionTypes,
                typeParametersMap.toBuilder().setValue(typeParameter, type).build());

        Map<TypeParameterDeclaration, Type> inferredTypes = new HashMap<>();
        for (int i = 0; i < paramTypes.size(); i++) {
            Type originalParamType = paramTypes.get(i);
            Type newParamType = originalParamType.replaceTypeVariables(typeParameter, type, inferredTypes);
            res = res.replaceParamType(i, newParamType);
        }
        for (int i = 0; i < exceptionTypes.size(); i++) {
            Type originalType = exceptionTypes.get(i);
            Type newType = originalType.replaceTypeVariables(typeParameter, type, inferredTypes);
            res = res.replaceExceptionType(i, newType);
        }
        Type oldReturnType = res.returnType;
        Type newReturnType = oldReturnType.replaceTypeVariables(typeParameter, type, inferredTypes);
        res = res.replaceReturnType(newReturnType);
        return res;
    }

    @Override
    public TypeParametersMap typeParametersMap() {
        return typeParametersMap;
    }

    public String getQualifiedSignature() {
        // TODO use the type parameters
        return this.getDeclaration().getQualifiedSignature();
    }

    public List<Type> exceptionTypes() {
        return exceptionTypes;
    }
}
