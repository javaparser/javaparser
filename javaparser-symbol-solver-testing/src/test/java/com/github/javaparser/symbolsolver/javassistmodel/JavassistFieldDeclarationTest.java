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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
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

    @Test
    void checkModifiersOnInterfaceFields() throws NotFoundException {
        CtClass tempInterface = ClassPool.getDefault().getCtClass("com.github.javaparser.symbolsolver.testingclasses.InterfaceWithFields");
        JavassistInterfaceDeclaration jcd = new JavassistInterfaceDeclaration(tempInterface, typeSolver);
        ResolvedFieldDeclaration resolvedField1 = jcd.getField("counter");

        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField1.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.ABSTRACT));

        ResolvedFieldDeclaration resolvedField2 = jcd.getField("counter1");

        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField2.hasModifier(Modifier.Keyword.ABSTRACT));
    }

    @Test
    void checkModifiersOnClassFields() throws NotFoundException {
        CtClass tempInterface = ClassPool.getDefault().getCtClass("com.github.javaparser.symbolsolver.testingclasses.ClassWithFields");
        JavassistClassDeclaration jcd = new JavassistClassDeclaration(tempInterface, typeSolver);
        ResolvedFieldDeclaration resolvedField1 = jcd.getField("counter");

        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.PUBLIC));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.STATIC));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField1.hasModifier(Modifier.Keyword.ABSTRACT));

        ResolvedFieldDeclaration resolvedField2 = jcd.getField("counter1");

        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.PUBLIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.STATIC));
        assertTrue(resolvedField2.hasModifier(Modifier.Keyword.FINAL));
        assertFalse(resolvedField2.hasModifier(Modifier.Keyword.ABSTRACT));
    }
}
