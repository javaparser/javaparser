/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import org.junit.jupiter.api.Test;

/**
 * Root-cause coverage for <a href="https://github.com/javaparser/javaparser/issues/5080">#5080</a>.
 *
 * <p>A parameterized {@link com.github.javaparser.resolution.types.ResolvedReferenceType} must substitute
 * its type arguments into method usages, symmetrically with what it already does for fields via
 * {@code getFieldType}. These tests exercise {@code getDeclaredMethods()} directly, independently of any
 * consumer-side compensation.
 */
class Issue5080Test extends AbstractResolutionTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();

    private ResolvedType type(String qualifiedName) {
        return new ReferenceTypeImpl(typeSolver.solveType(qualifiedName));
    }

    private ReferenceTypeImpl genericType(String qualifiedName, ResolvedType... args) {
        return new ReferenceTypeImpl(typeSolver.solveType(qualifiedName), Arrays.asList(args));
    }

    private MethodUsage method(ReferenceTypeImpl type, String name, int arity) {
        return type.getDeclaredMethods().stream()
                .filter(m -> m.getName().equals(name) && m.getNoParams() == arity)
                .findFirst()
                .orElseThrow(AssertionError::new);
    }

    /**
     * {@code List<String>.get(int)} must report {@code String} as its return type, not the raw type
     * variable {@code E} — the method-level counterpart of the field substitution done by getFieldType.
     */
    @Test
    void declaredMethodReturnTypeIsSubstituted() {
        ReferenceTypeImpl listOfString = genericType("java.util.List", type("java.lang.String"));
        assertEquals(
                "java.lang.String", method(listOfString, "get", 1).returnType().describe());
    }

    /**
     * {@code List<String>.add(E)} must report {@code String} as its parameter type.
     */
    @Test
    void declaredMethodParameterTypeIsSubstituted() {
        ReferenceTypeImpl listOfString = genericType("java.util.List", type("java.lang.String"));
        assertEquals(
                "java.lang.String",
                method(listOfString, "add", 1).getParamType(0).describe());
    }

    /**
     * {@code List<String>.<T>toArray(T[])} is generic on the method's own type variable {@code T};
     * substituting the type's argument must NOT touch it.
     */
    @Test
    void methodLevelTypeParameterIsNotSubstituted() {
        ReferenceTypeImpl listOfString = genericType("java.util.List", type("java.lang.String"));
        String returnType = method(listOfString, "toArray", 1).returnType().describe();
        assertTrue(returnType.contains("T"), "method-level type parameter must not be substituted, was: " + returnType);
    }
}
