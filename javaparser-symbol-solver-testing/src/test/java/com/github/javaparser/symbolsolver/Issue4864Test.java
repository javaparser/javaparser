/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.*;
import java.lang.reflect.Method;
import java.lang.reflect.TypeVariable;
import org.junit.jupiter.api.Test;

public class Issue4864Test {
    private final TypeSolver typeSolver = null;

    @Test
    void testReflectionInterfaceDeclarationToString() {
        ReflectionInterfaceDeclaration decl = new ReflectionInterfaceDeclaration(Runnable.class, typeSolver);
        String output = decl.toString();

        assertTrue(output.contains("ReflectionInterfaceDeclaration"));
        assertTrue(output.contains("clazz=java.lang.Runnable"));
    }

    @Test
    void testReflectionClassDeclarationToString() {
        ReflectionClassDeclaration decl = new ReflectionClassDeclaration(String.class, typeSolver);
        String output = decl.toString();

        assertTrue(output.contains("ReflectionClassDeclaration"));
        assertTrue(output.contains("clazz="));
        assertTrue(output.contains("java.lang.String"));
    }

    @Test
    void testReflectionParameterDeclarationToString() {
        ReflectionParameterDeclaration decl =
                new ReflectionParameterDeclaration(String.class, String.class, typeSolver, false, "param1");
        String output = decl.toString();

        assertTrue(output.contains("ReflectionParameterDeclaration"));
        assertTrue(output.contains("type=class java.lang.String"));
        assertTrue(output.contains("name=param1"));
    }

    @Test
    void testReflectionTypeParameterToString() {
        TypeVariable<Class<Comparable>> typeVar = Comparable.class.getTypeParameters()[0];
        ReflectionTypeParameter param = new ReflectionTypeParameter(typeVar, true, typeSolver);
        String output = param.toString();

        assertTrue(output.contains("ReflectionTypeParameter"));
        assertTrue(output.contains("typeVariable="));
        assertTrue(output.contains("T"));
    }

    @Test
    void testReflectionMethodDeclarationToString() throws NoSuchMethodException {
        Method method = String.class.getMethod("substring", int.class, int.class);
        ReflectionMethodDeclaration decl = new ReflectionMethodDeclaration(method, typeSolver);
        String output = decl.toString();

        assertTrue(output.contains("ReflectionMethodDeclaration"));
        assertTrue(output.contains("method=public java.lang.String java.lang.String.substring(int,int)"));
    }
}
