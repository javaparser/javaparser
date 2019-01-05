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

import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.stream.Collectors;

import static java.util.Comparator.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ReflectionInterfaceDeclarationTest extends AbstractSymbolResolutionTest {

    @Test
    void testGetDeclaredMethods() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        List<ResolvedMethodDeclaration> methods = list.getDeclaredMethods().stream()
                .sorted(comparing(ResolvedDeclaration::getName))
                .collect(Collectors.toList());
        int foundCount = 0;
        for (ResolvedMethodDeclaration method : methods) {
            switch (method.getName()) {
                case "clear":
                    assertTrue(method.isAbstract());
                    assertEquals(0, method.getNumberOfParams());
                    foundCount++;
                    break;
                case "contains":
                    assertEquals(true, method.isAbstract());
                    assertEquals(1, method.getNumberOfParams());
                    assertEquals(true, method.getParam(0).getType().isReferenceType());
                    assertEquals(Object.class.getCanonicalName(), method.getParam(0).getType().asReferenceType().getQualifiedName());
                    foundCount++;
                    break;
            }
        }
        assertEquals(2, foundCount);
    }

    @Test
    void testAllAncestors() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        list.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(3, ancestors.size());

        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(list.getTypeParameters().get(0));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.lang.Iterable"));
    }

}
