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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.Test;

import java.nio.Buffer;
import java.nio.CharBuffer;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static java.util.Comparator.comparing;
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
        assertEquals(2, ancestors.size());

        // Since List is an interface, Object cannot be an ancestor of List
        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(list.getTypeParameters().get(0));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(typeVariable)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(typeVariable)), ancestors.get("java.lang.Iterable"));
    }
    
	@Test
	void testAllAncestorsForAnInterfaceWithBreadthFirstFunc() {
		TypeSolver typeResolver = new ReflectionTypeSolver();
		ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
		List<ResolvedReferenceType> ancestors = list.getAllAncestors(ResolvedReferenceTypeDeclaration.breadthFirstFunc);
		assertEquals(2, ancestors.size());

		ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(list.getTypeParameters().get(0));
		assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver),
				ImmutableList.of(typeVariable)), ancestors.get(0));
		assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver),
				ImmutableList.of(typeVariable)), ancestors.get(1));
	}
	
	@Test
	void testAllAncestorsForAClassWithBreadthFirstFunc() {
		TypeSolver typeResolver = new ReflectionTypeSolver();
		ReflectionClassDeclaration obj = new ReflectionClassDeclaration(CharBuffer.class, typeResolver);
		List<ResolvedReferenceType> ancestors = obj.getAllAncestors(ResolvedReferenceTypeDeclaration.breadthFirstFunc);
		assertEquals(6, ancestors.size());

		assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Buffer.class, typeResolver)),
				ancestors.get(0));
		assertEquals(
				new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Appendable.class, typeResolver)),
				ancestors.get(2));
		assertEquals(
				new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(CharSequence.class, typeResolver)),
				ancestors.get(3));
		assertEquals(
				new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Readable.class, typeResolver)),
				ancestors.get(4));
		assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver)),
				ancestors.get(5));
	}

}
