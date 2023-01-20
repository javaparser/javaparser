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

public interface ResolvedDeclarationTest extends AssociableToASTTest {

    ResolvedDeclaration createValue();

    @Test
    default void whenNameIsPresentACallForMethodGetNameShouldNotBeNull() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.hasName())
            assertNotNull(resolvedDeclaration.getName());
        else
            assertNull(resolvedDeclaration.getName());
    }

    @Test
    default void whenDeclarationIsAFieldTheCallToTheMethodAsFieldShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isField())
            assertDoesNotThrow(resolvedDeclaration::asField);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asField);
    }

    @Test
    default void whenDeclarationIsAMethodTheCallToTheMethodAsMethodShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isMethod())
            assertDoesNotThrow(resolvedDeclaration::asMethod);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asMethod);
    }

    @Test
    default void whenDeclarationIsAParameterTheCallToTheMethodAsParameterShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isParameter())
            assertDoesNotThrow(resolvedDeclaration::asParameter);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asParameter);
    }

    @Test
    default void whenDeclarationIsAPatternTheCallToTheMethodAsPatternShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isPattern())
            assertDoesNotThrow(resolvedDeclaration::asPattern);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asPattern);
    }

    @Test
    default void whenDeclarationIsAEnumConstantTheCallToTheMethodAsEnumConstantShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isEnumConstant())
            assertDoesNotThrow(resolvedDeclaration::asEnumConstant);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asEnumConstant);
    }

    @Test
    default void whenDeclarationIsATypeTheCallToTheMethodAsTypeShouldNotThrow() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        if (resolvedDeclaration.isType())
            assertDoesNotThrow(resolvedDeclaration::asType);
        else
            assertThrows(UnsupportedOperationException.class, resolvedDeclaration::asType);
    }

    /**
     * According to the documentation in {@link AssociableToAST#toAst()}
     * all the Resolved declaration most be associable to a AST.
     *
     * @see AssociableToAST#toAst()
     */
    @Test
    default void declarationMostBeAssociableToAST() {
        ResolvedDeclaration resolvedDeclaration = createValue();
        assertTrue(resolvedDeclaration instanceof AssociableToAST);
    }

}
