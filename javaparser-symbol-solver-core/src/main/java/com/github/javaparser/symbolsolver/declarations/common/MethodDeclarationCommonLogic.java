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

package com.github.javaparser.symbolsolver.declarations.common;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.logic.InferenceContext;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class MethodDeclarationCommonLogic {

    private ResolvedMethodDeclaration methodDeclaration;
    private TypeSolver typeSolver;

    public MethodDeclarationCommonLogic(ResolvedMethodDeclaration methodDeclaration, TypeSolver typeSolver) {
        this.methodDeclaration = methodDeclaration;
        this.typeSolver = typeSolver;
    }

    public MethodUsage resolveTypeVariables(Context context, List<ResolvedType> parameterTypes) {
        ResolvedType returnType = replaceTypeParams(methodDeclaration.getReturnType(), context);
        List<ResolvedType> params = new ArrayList<>();
        for (int i = 0; i < methodDeclaration.getNumberOfParams(); i++) {
            ResolvedType replaced = replaceTypeParams(methodDeclaration.getParam(i).getType(), context);
            params.add(replaced);
        }

        // We now look at the type parameter for the method which we can derive from the parameter types
        // and then we replace them in the return type
        // Map<TypeParameterDeclaration, Type> determinedTypeParameters = new HashMap<>();
        InferenceContext inferenceContext = new InferenceContext(MyObjectProvider.INSTANCE);
        for (int i = 0; i < methodDeclaration.getNumberOfParams() - (methodDeclaration.hasVariadicParameter() ? 1 : 0); i++) {
            ResolvedType formalParamType = methodDeclaration.getParam(i).getType();
            ResolvedType actualParamType = parameterTypes.get(i);
            inferenceContext.addPair(formalParamType, actualParamType);
        }

        returnType = inferenceContext.resolve(inferenceContext.addSingle(returnType));

        return new MethodUsage(methodDeclaration, params, returnType);
    }

    private ResolvedType replaceTypeParams(ResolvedType type, Context context) {
        if (type.isTypeVariable()) {
            ResolvedTypeParameterDeclaration typeParameter = type.asTypeParameter();
            if (typeParameter.declaredOnType()) {
                Optional<ResolvedType> typeParam = typeParamByName(typeParameter.getName(), context);
                if (typeParam.isPresent()) {
                    type = typeParam.get();
                }
            }
        }

        if (type.isReferenceType()) {
            type.asReferenceType().transformTypeParameters(tp -> replaceTypeParams(tp, context));
        }

        return type;
    }

    protected Optional<ResolvedType> typeParamByName(String name, Context context) {
        return methodDeclaration.getTypeParameters().stream().filter(tp -> tp.getName().equals(name)).map(tp -> toType(tp)).findFirst();
    }

    protected ResolvedType toType(ResolvedTypeParameterDeclaration typeParameterDeclaration) {
        return new ResolvedTypeVariable(typeParameterDeclaration);
    }
}
