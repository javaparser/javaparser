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

import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class ReflectionInterfaceDeclarationTest {

    @Test
    public void testGetDeclaredMethods() {
        TypeSolver typeResolver = new JreTypeSolver();
        TypeDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        List<MethodDeclaration> methods = list.getDeclaredMethods().stream()
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        assertEquals(28, methods.size());
        assertEquals("clear", methods.get(4).getName());
        assertEquals(true, methods.get(4).isAbstract());
        assertEquals(0, methods.get(4).getNoParams());
        assertEquals("contains", methods.get(5).getName());
        assertEquals(true, methods.get(5).isAbstract());
        assertEquals(1, methods.get(5).getNoParams());
        assertEquals(true, methods.get(5).getParam(0).getType().isReferenceType());
        assertEquals(Object.class.getCanonicalName(), methods.get(5).getParam(0).getType().asReferenceType().getQualifiedName());
    }

}
