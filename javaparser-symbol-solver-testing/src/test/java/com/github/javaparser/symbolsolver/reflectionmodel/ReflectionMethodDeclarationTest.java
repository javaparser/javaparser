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
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class ReflectionMethodDeclarationTest {

    @Test
    void testParameterNameOnClassesFromTheStdLibrary() {
        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration object = new ReflectionClassDeclaration(Object.class, typeResolver);
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);

        ResolvedMethodDeclaration equals = object.getAllMethods().stream().filter(m -> m.getName().equals("equals")).findFirst().get().getDeclaration();
        ResolvedMethodDeclaration containsAll = list.getAllMethods().stream().filter(m -> m.getName().equals("containsAll")).findFirst().get().getDeclaration();
        ResolvedMethodDeclaration subList = list.getAllMethods().stream().filter(m -> m.getName().equals("subList")).findFirst().get().getDeclaration();

        assertEquals("arg0", equals.getParam(0).getName());
        assertEquals("arg0", containsAll.getParam(0).getName());
        assertEquals("arg0", subList.getParam(0).getName());
        assertEquals("arg1", subList.getParam(1).getName());
    }

    class Foo {
        void myMethod(int a, char c) {

        }
    }

    @Test
    void testParameterNameOnClassesFromThisProject() {
        TypeSolver typeResolver = new ReflectionTypeSolver(false);

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        ResolvedMethodDeclaration myMethod = foo.getAllMethods().stream().filter(m -> m.getName().equals("myMethod")).findFirst().get().getDeclaration();

        assertEquals("arg0", myMethod.getParam(0).getName());
        assertEquals("arg1", myMethod.getParam(1).getName());
    }

}
