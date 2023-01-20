/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.resolution.declarations;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public interface ResolvedTypeDeclarationTest extends ResolvedDeclarationTest {

    @Override
    ResolvedTypeDeclaration createValue();

    @Test
    default void whenDeclarationIsAClassTheCallToTheMethodAsClassShouldNotThrow() {
        ResolvedTypeDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isClass())
            assertDoesNotThrow(resolvedDeclaration::asClass);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asClass);
    }

    @Test
    default void whenDeclarationIsAInterfaceTheCallToTheMethodAsInterfaceShouldNotThrow() {
        ResolvedTypeDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isInterface())
            assertDoesNotThrow(resolvedDeclaration::asInterface);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asInterface);
    }

    @Test
    default void whenDeclarationIsAEnumTheCallToTheMethodAsEnumShouldNotThrow() {
        ResolvedTypeDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isEnum())
            assertDoesNotThrow(resolvedDeclaration::asEnum);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asEnum);
    }

    @Test
    default void whenDeclarationIsATypeParameterTheCallToTheMethodAsTypeParameterShouldNotThrow() {
        ResolvedTypeDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isTypeParameter())
            assertDoesNotThrow(resolvedDeclaration::asTypeParameter);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asTypeParameter);
    }

    @Test
    default void whenDeclarationIsAReferenceTypeTheCallToTheMethodAsReferenceTypeShouldNotThrow() {
        ResolvedTypeDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isReferenceType())
            assertDoesNotThrow(resolvedDeclaration::asReferenceType);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asReferenceType);
    }

    @Test
    default void qualifiedNameCantBeNull() {
        assertNotNull(createValue().getQualifiedName());
    }

    @Test
    default void getIdCantBeNull() {
        assertNotNull(createValue().getId());
    }

    @Test
    default void containerTypeCantBeNull() {
        assertNotNull(createValue().containerType());
    }

}
