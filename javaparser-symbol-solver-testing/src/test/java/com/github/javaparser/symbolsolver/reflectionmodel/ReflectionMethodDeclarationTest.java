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

import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
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
