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

import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class ReflectionInterfaceDeclarationTest extends AbstractTest {

    @Test
    public void testGetDeclaredMethods() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        List<ResolvedMethodDeclaration> methods = list.getDeclaredMethods().stream()
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        if (isJava9()) {
            assertEquals(40, methods.size());
            assertEquals("clear", methods.get(4).getName());
            assertEquals(true, methods.get(4).isAbstract());
            assertEquals(0, methods.get(4).getNumberOfParams());
            assertEquals("contains", methods.get(5).getName());
            assertEquals(true, methods.get(5).isAbstract());
            assertEquals(1, methods.get(5).getNumberOfParams());
            assertEquals(true, methods.get(5).getParam(0).getType().isReferenceType());
            assertEquals(Object.class.getCanonicalName(), methods.get(5).getParam(0).getType().asReferenceType().getQualifiedName());
        } else {
            assertEquals(28, methods.size());
            assertEquals("clear", methods.get(4).getName());
            assertEquals(true, methods.get(4).isAbstract());
            assertEquals(0, methods.get(4).getNumberOfParams());
            assertEquals("contains", methods.get(5).getName());
            assertEquals(true, methods.get(5).isAbstract());
            assertEquals(1, methods.get(5).getNumberOfParams());
            assertEquals(true, methods.get(5).getParam(0).getType().isReferenceType());
            assertEquals(Object.class.getCanonicalName(), methods.get(5).getParam(0).getType().asReferenceType().getQualifiedName());
        }
    }

    @Test
    public void testAllAncestors() {
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
