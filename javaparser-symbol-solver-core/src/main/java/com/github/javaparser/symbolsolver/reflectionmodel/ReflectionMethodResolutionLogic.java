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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class ReflectionMethodResolutionLogic {

    static SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes, boolean staticOnly,
                                                                  TypeSolver typeSolver, ResolvedReferenceTypeDeclaration scopeType,
                                                                  Class clazz){
        List<ResolvedMethodDeclaration> methods = new ArrayList<>();
        Predicate<Method> staticOnlyCheck = m -> !staticOnly || (staticOnly && Modifier.isStatic(m.getModifiers()));
        for (Method method : clazz.getMethods()) {
            if (method.isBridge() || method.isSynthetic() || !method.getName().equals(name)|| !staticOnlyCheck.test(method)) continue;
            ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);
        }

        for (ResolvedReferenceType ancestor : scopeType.getAncestors()) {
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(ancestor.getTypeDeclaration(), name, parameterTypes, staticOnly);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }

        if (scopeType.getAncestors().isEmpty()){
            ReferenceTypeImpl objectClass = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(objectClass.getTypeDeclaration(), name, parameterTypes, staticOnly);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        return MethodResolutionLogic.findMostApplicable(methods, name, parameterTypes, typeSolver);
    }

    static Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver,
                                                    Context invokationContext, List<ResolvedType> typeParameterValues,
                                                    ResolvedReferenceTypeDeclaration scopeType, Class clazz) {
        if (typeParameterValues.size() != scopeType.getTypeParameters().size()) {
            // if it is zero we are going to ignore them
            if (!scopeType.getTypeParameters().isEmpty()) {
                // Parameters not specified, so default to Object
                typeParameterValues = new ArrayList<>();
                for (int i = 0; i < scopeType.getTypeParameters().size(); i++) {
                    typeParameterValues.add(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver));
                }
            }
        }
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : clazz.getMethods()) {
            if (method.getName().equals(name) && !method.isBridge() && !method.isSynthetic()) {
                ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
                MethodUsage methodUsage = replaceParams(typeParameterValues, scopeType, methodDeclaration);
                methods.add(methodUsage);
            }

        }

        for(ResolvedReferenceType ancestor : scopeType.getAncestors()){
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(ancestor.getTypeDeclaration(), name, argumentsTypes);
            if (ref.isSolved()){
                ResolvedMethodDeclaration correspondingDeclaration = ref.getCorrespondingDeclaration();
                MethodUsage methodUsage = replaceParams(typeParameterValues, ancestor.getTypeDeclaration(), correspondingDeclaration);
                methods.add(methodUsage);
            }
        }

        if (scopeType.getAncestors().isEmpty()){
            ReferenceTypeImpl objectClass = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(objectClass.getTypeDeclaration(), name, argumentsTypes);
            if (ref.isSolved()) {
                MethodUsage usage = replaceParams(typeParameterValues, objectClass.getTypeDeclaration(), ref.getCorrespondingDeclaration());
                methods.add(usage);
            }
        }

        final List<ResolvedType> finalTypeParameterValues = typeParameterValues;
        argumentsTypes = argumentsTypes.stream().map((pt) -> {
            int i = 0;
            for (ResolvedTypeParameterDeclaration tp : scopeType.getTypeParameters()) {
                pt = pt.replaceTypeVariables(tp, finalTypeParameterValues.get(i));
                i++;
            }
            return pt;
        }).collect(Collectors.toList());
        return MethodResolutionLogic.findMostApplicableUsage(methods, name, argumentsTypes, typeSolver);
    }

    private static MethodUsage replaceParams(List<ResolvedType> typeParameterValues, ResolvedReferenceTypeDeclaration typeParametrizable, ResolvedMethodDeclaration methodDeclaration) {
        MethodUsage methodUsage = new MethodUsage(methodDeclaration);
        int i = 0;

        // Only replace if we have enough values provided
        if (typeParameterValues.size() == typeParametrizable.getTypeParameters().size()){
            for (ResolvedTypeParameterDeclaration tp : typeParametrizable.getTypeParameters()) {
                methodUsage = methodUsage.replaceTypeParameter(tp, typeParameterValues.get(i));
                i++;
            }
        }

        for (ResolvedTypeParameterDeclaration methodTypeParameter : methodDeclaration.getTypeParameters()) {
            methodUsage = methodUsage.replaceTypeParameter(methodTypeParameter, new ResolvedTypeVariable(methodTypeParameter));
        }

        return methodUsage;
    }
}
