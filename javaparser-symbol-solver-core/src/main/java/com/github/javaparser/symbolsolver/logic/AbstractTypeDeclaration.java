/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
            List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> typeParametersMap =
                    ancestor.getTypeParametersMap();
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

    /**
     * With the introduction of records in Java 14 (Preview), the {@code Class.isRecord} method
     * was added to check whether a class is a record or not (similar to {@code isEnum} etc.).
     * This method cannot be used directly in JavaParser, however, since it will not compile
     * on Java versions 8-13 (or 15 if preview features aren't enabled) which are supported
     * by the project.
     *
     * This workaround calls the {@code isRecord} method via reflection which compiles while still
     * giving the expected answer. There are 2 cases to consider when this method is called:
     *
     * 1) JavaParser is invoked using a Java runtime which supports records
     *    In this case, the {@code isRecord} method exists, so invoking it will give the
     *    answer as usual.
     *
     * 2) JavaParser is invoked using an older Java runtime without record support
     *    In this case, the {@code isRecord} method does not exist, so attempting to invoke
     *    it will throw a {@code NoSuchMethodException}. This is not a problem since the
     *    classloader cannot load classes compiled by Java versions greater than that used
     *    to invoke JavaParser. This means that if JavaParser is invoked with a Java 8 runtime,
     *    for example, then no classes compiled with Java versions greater than 8 are supported,
     *    so no class loaded by the classloader could possibly be a record class since it could
     *    not be compiled in the first place. There may be an edge case here for classes compiled
     *    with Java 14/15 preview, but most likely these won't load either.
     *
     *    In the case of an {@code NoSuchMethodException}, simply return false as the type could
     *    not be a record for the reason explained above.
     */
    public static boolean isRecordType(Class<?> clazz) {
        try {
            Method isRecord = Class.class.getMethod("isRecord");
            return (Boolean) isRecord.invoke(clazz);
        } catch (NoSuchMethodException e) {
            return false;
        } catch (InvocationTargetException | IllegalAccessException e) {
            // These exceptions should never be thrown since a known standard library function is
            // being invoked, so if this happens something went wrong.
            Log.error("Could not invoke isRecord on " + clazz.getName() + " due to " + e.getMessage());
            return false;
        }
    }
}
