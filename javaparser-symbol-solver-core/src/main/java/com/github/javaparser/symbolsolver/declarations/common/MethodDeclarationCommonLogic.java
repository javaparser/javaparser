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

package com.github.javaparser.symbolsolver.declarations.common;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
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
        for (int i = 0; i < methodDeclaration.getNumberOfParams(); i++) {
            ResolvedParameterDeclaration formalParamDecl = methodDeclaration.getParam(i);
            ResolvedType formalParamType = formalParamDecl.getType();

            // Don't continue if a vararg parameter is reached and there are no arguments left
            if (formalParamDecl.isVariadic() && parameterTypes.size() < methodDeclaration.getNumberOfParams()) {
                break;
            }

            ResolvedType actualParamType = parameterTypes.get(i);

            if (formalParamDecl.isVariadic() && !actualParamType.isArray()) {
                formalParamType = formalParamType.asArrayType().getComponentType();
            }

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
