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
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ReflectionFieldDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver(false);

    @Test
    void verifyIsVolatileVariableDeclaration() {
        ReflectionClassDeclaration rcd = new ReflectionClassDeclaration(AtomicBoolean.class, typeSolver);
        assertTrue(rcd.getField("value").isVolatile());
    }
    
    @Test
    void verifyIsNotVolatileVariableDeclaration() {
        ReflectionClassDeclaration rcd = new ReflectionClassDeclaration(String.class, typeSolver);
        assertFalse(rcd.getField("serialVersionUID").isVolatile());
    }
}
