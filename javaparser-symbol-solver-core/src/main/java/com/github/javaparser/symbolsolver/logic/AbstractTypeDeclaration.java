/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.utils.Pair;

/**
 * Common ancestor for most types.
 *
 * @author Federico Tomassetti
 */
public abstract class AbstractTypeDeclaration implements ResolvedReferenceTypeDeclaration {

	/*
	 * Returns all methods which have distinct "enhanced" signature declared in this type and all members.
	 * An "enhanced" signature include the return type which is used sometimes to identify functional interfaces.
	 * This is a different implementation from the previous one which returned all methods which have a distinct
	 * signature (based on method name and qualified parameter types)
	 */
    @Override
    public final Set<MethodUsage> getAllMethods() {
        Set<MethodUsage> methods = new HashSet<>();

        Set<String> methodsSignatures = new HashSet<>();

        for (ResolvedMethodDeclaration methodDeclaration : getDeclaredMethods()) {
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            methods.add(methodUsage);
            String signature = methodUsage.getSignature();
            String returnType = methodUsage.getDeclaration().getReturnType().describe();
            String enhancedSignature = String.format("%s %s", returnType, signature);
            methodsSignatures.add(enhancedSignature);
        }

        for (ResolvedReferenceType ancestor : getAllAncestors()) {
            List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> typeParametersMap = ancestor.getTypeParametersMap();
            for (MethodUsage mu : ancestor.getDeclaredMethods()) {
                // replace type parameters to be able to filter away overridden generified methods
                MethodUsage methodUsage = mu;
                for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> p : typeParametersMap) {
                    methodUsage = methodUsage.replaceTypeParameter(p.a, p.b);
                }
                String signature = methodUsage.getSignature();
                String returnType = methodUsage.getDeclaration().getReturnType().describe();
                String enhancedSignature = String.format("%s %s", returnType, signature);
                if (!methodsSignatures.contains(enhancedSignature)) {
                    methodsSignatures.add(enhancedSignature);
                    methods.add(mu);
                }
            }
        }

        return methods;
    }

    @Override
    public final boolean isFunctionalInterface() {
        return FunctionalInterfaceLogic.getFunctionalMethod(this).isPresent();
    }

}
