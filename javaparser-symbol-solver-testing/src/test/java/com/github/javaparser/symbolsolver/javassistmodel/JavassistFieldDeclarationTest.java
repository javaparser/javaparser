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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.NotFoundException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavassistFieldDeclarationTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver(false);

    @Test
    void verifyIsVolatileVariableDeclarationFromJavassist() throws NotFoundException {
        CtClass clazz = ClassPool.getDefault().getCtClass("java.util.concurrent.atomic.AtomicBoolean");
        JavassistClassDeclaration jcd = new JavassistClassDeclaration(clazz, typeSolver);
        assertTrue(jcd.getField("value").isVolatile());
    }
    
    @Test
    void verifyIsNotVolatileVariableDeclarationFromJavassist() throws NotFoundException {
        CtClass clazz = ClassPool.getDefault().getCtClass("java.lang.String");
        JavassistClassDeclaration jcd = new JavassistClassDeclaration(clazz, typeSolver);
        assertFalse(jcd.getField("serialVersionUID").isVolatile());
    }
    
}
