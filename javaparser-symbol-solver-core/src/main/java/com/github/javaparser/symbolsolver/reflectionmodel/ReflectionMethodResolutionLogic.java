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
            ancestor.getTypeDeclaration().ifPresent(ancestorTypeDeclaration -> {
                SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(ancestorTypeDeclaration, name, parameterTypes, staticOnly);
                if (ref.isSolved()) {
                    methods.add(ref.getCorrespondingDeclaration());
                }
            });
        }

        if (scopeType.getAncestors().isEmpty()){
            ReferenceTypeImpl objectClass = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
            objectClass.getTypeDeclaration().ifPresent(objectTypeDeclaration -> {
                SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(objectTypeDeclaration, name, parameterTypes, staticOnly);
                if (ref.isSolved()) {
                    methods.add(ref.getCorrespondingDeclaration());
                }
            });
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
            if(ancestor.getTypeDeclaration().isPresent()) {
                ResolvedReferenceTypeDeclaration ancestorTypeDeclaration = ancestor.getTypeDeclaration().get();
                SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(ancestorTypeDeclaration, name, argumentsTypes);
                if (ref.isSolved()){
                    ResolvedMethodDeclaration correspondingDeclaration = ref.getCorrespondingDeclaration();
                    MethodUsage methodUsage = replaceParams(typeParameterValues, ancestorTypeDeclaration, correspondingDeclaration);
                    methods.add(methodUsage);
                }
            }
        }

        if (scopeType.getAncestors().isEmpty()) {
            Optional<ResolvedReferenceTypeDeclaration> optionalObjectClass = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver).getTypeDeclaration();
            if (optionalObjectClass.isPresent()) {
                SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(optionalObjectClass.get(), name, argumentsTypes);
                if (ref.isSolved()) {
                    MethodUsage usage = replaceParams(typeParameterValues, optionalObjectClass.get(), ref.getCorrespondingDeclaration());
                    methods.add(usage);
                }
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
