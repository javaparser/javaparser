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

package com.github.javaparser.resolution.logic;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.lang.reflect.Method;
import java.lang.reflect.Parameter;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public final class FunctionalInterfaceLogic {
    
    private static String JAVA_LANG_FUNCTIONAL_INTERFACE = FunctionalInterface.class.getCanonicalName();

    private FunctionalInterfaceLogic() {
        // prevent instantiation
    }

    /**
     * Get the functional method defined by the type, if any.
     */
    public static Optional<MethodUsage> getFunctionalMethod(ResolvedType type) {
        Optional<ResolvedReferenceTypeDeclaration> optionalTypeDeclaration = type.asReferenceType().getTypeDeclaration();
        if(!optionalTypeDeclaration.isPresent()) {
            return Optional.empty();
        }

        ResolvedReferenceTypeDeclaration typeDeclaration = optionalTypeDeclaration.get();
        if (type.isReferenceType() && typeDeclaration.isInterface()) {
            return getFunctionalMethod(typeDeclaration);
        } else {
            return Optional.empty();
        }
    }

    /**
     * Get the functional method defined by the type, if any.
     */
    public static Optional<MethodUsage> getFunctionalMethod(ResolvedReferenceTypeDeclaration typeDeclaration) {
        //We need to find all abstract methods
        Set<MethodUsage> methods = typeDeclaration.getAllMethods().stream()
                .filter(m -> m.getDeclaration().isAbstract())
                // Remove methods inherited by Object:
                // Consider the case of Comparator which define equals. It would be considered a functional method.
                .filter(m -> !declaredOnObject(m))
                .collect(Collectors.toSet());

        if (methods.size() == 1) {
            return Optional.of(methods.iterator().next());
        } else {
            return Optional.empty();
        }
    }

    public static boolean isFunctionalInterfaceType(ResolvedType type) {
        if (type.isReferenceType()) {
            Optional<ResolvedReferenceTypeDeclaration> optionalTypeDeclaration = type.asReferenceType().getTypeDeclaration();
            if (optionalTypeDeclaration.isPresent() && optionalTypeDeclaration.get().hasAnnotation(JAVA_LANG_FUNCTIONAL_INTERFACE)) {
                return true;
            }
        }
        return getFunctionalMethod(type).isPresent();
    }

    private static String getSignature(Method m) {
        return String.format("%s(%s)", m.getName(), String.join(", ", Arrays.stream(m.getParameters()).map(p -> toSignature(p)).collect(Collectors.toList())));
    }

    private static String toSignature(Parameter p) {
        return p.getType().getCanonicalName();
    }

    private static List<String> OBJECT_METHODS_SIGNATURES = Arrays.stream(Object.class.getDeclaredMethods())
            .map(method -> getSignature(method))
            .collect(Collectors.toList());

    private static boolean declaredOnObject(MethodUsage m) {
        return OBJECT_METHODS_SIGNATURES.contains(m.getDeclaration().getSignature());
    }
}
