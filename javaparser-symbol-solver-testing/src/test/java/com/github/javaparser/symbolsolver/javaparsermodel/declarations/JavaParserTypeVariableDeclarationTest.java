/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2021 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserTypeVariableDeclarationTest {

    private JavaParserTypeVariableDeclaration createValue() {
        TypeParameter typeParameter = new TypeParameter();
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserTypeVariableDeclaration(typeParameter, typeSolver);
    }

    @Test
    void isTypeShouldBeTrue() {
        assertTrue(createValue().isType());
    }

    @Test
    void isTypeParameterShouldBeTrue() {
        assertTrue(createValue().isTypeParameter());
    }

    @Test
    void isParameterShouldBeFalse() {
        assertFalse(createValue().isParameter());
    }

    @Test
    void isFieldShouldBeFalse() {
        assertFalse(createValue().isField());
    }

    @Test
    void isClassShouldBeFalse() {
        assertFalse(createValue().isClass());
    }

    @Test
    void isInterfaceShouldBeFalse() {
        assertFalse(createValue().isInterface());
    }

}