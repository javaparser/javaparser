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

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.util.*;
import java.util.stream.Collectors;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

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
                .filter(m -> !isPublicMemberOfObject(m))
                .collect(Collectors.toSet());
        // TODO a functional interface can have multiple subsignature method with a return-type-substitutable
        // see https://docs.oracle.com/javase/specs/jls/se8/html/jls-9.html#jls-9.8
        if (methods.size() == 0) {
        	return Optional.empty();
        }
        Iterator<MethodUsage> iterator = methods.iterator();
        MethodUsage methodUsage = iterator.next();
        while (iterator.hasNext()) {
        	MethodUsage otherMethodUsage = iterator.next();
        	if (!(methodUsage.isSameSignature(otherMethodUsage)
        			|| methodUsage.isSubSignature(otherMethodUsage)
        			|| otherMethodUsage.isSubSignature(methodUsage))) {
        		methodUsage = null;
        		break;
        	}
        	if (!(methodUsage.isReturnTypeSubstituable(otherMethodUsage))) {
        		methodUsage = null;
        		break;
        	}
        }
        return Optional.ofNullable(methodUsage);
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

    private static List<String> OBJECT_PUBLIC_METHODS_SIGNATURES = Arrays.stream(Object.class.getDeclaredMethods())
    		.filter(m -> Modifier.isPublic(m.getModifiers()))
            .map(method -> getSignature(method))
            .collect(Collectors.toList());

    private static boolean isPublicMemberOfObject(MethodUsage m) {
        return OBJECT_PUBLIC_METHODS_SIGNATURES.contains(m.getDeclaration().getSignature());
    }
}
