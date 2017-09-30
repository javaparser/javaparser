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
import org.junit.Test;

import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class ReflectionMethodDeclarationTest {

    @Test
    public void testGetSignature() {
        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration object = new ReflectionClassDeclaration(Object.class, typeResolver);
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);

        ResolvedMethodDeclaration hashCode = object.getAllMethods().stream().filter(m -> m.getName().equals("hashCode")).findFirst().get().getDeclaration();
        ResolvedMethodDeclaration equals = object.getAllMethods().stream().filter(m -> m.getName().equals("equals")).findFirst().get().getDeclaration();
        ResolvedMethodDeclaration containsAll = list.getAllMethods().stream().filter(m -> m.getName().equals("containsAll")).findFirst().get().getDeclaration();
        ResolvedMethodDeclaration subList = list.getAllMethods().stream().filter(m -> m.getName().equals("subList")).findFirst().get().getDeclaration();

        assertEquals("hashCode()", hashCode.getSignature());
        assertEquals("equals(java.lang.Object)", equals.getSignature());
        assertEquals("containsAll(java.util.Collection<? extends java.lang.Object>)", containsAll.getSignature());
        assertEquals("subList(int, int)", subList.getSignature());
    }

    @Test
    public void testGetGenericReturnType() {
        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedInterfaceDeclaration map = new ReflectionInterfaceDeclaration(Map.class, typeResolver);

        ResolvedMethodDeclaration put = map.getAllMethods().stream().filter(m -> m.getName().equals("put")).findFirst().get().getDeclaration();
        assertEquals(true, put.getReturnType().isTypeVariable());
        assertEquals(true, put.getReturnType().asTypeParameter().declaredOnType());
        assertEquals("java.util.Map.V", put.getReturnType().asTypeParameter().getQualifiedName());
    }

    @Test
    public void testGetGenericParameters() {
        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedInterfaceDeclaration map = new ReflectionInterfaceDeclaration(Map.class, typeResolver);

        ResolvedMethodDeclaration put = map.getAllMethods().stream().filter(m -> m.getName().equals("put")).findFirst().get().getDeclaration();
        assertEquals(true, put.getParam(0).getType().isTypeVariable());
        assertEquals(true, put.getParam(0).getType().asTypeParameter().declaredOnType());
        assertEquals("java.util.Map.K", put.getParam(0).getType().asTypeParameter().getQualifiedName());

        assertEquals(true, put.getParam(1).getType().isTypeVariable());
        assertEquals(true, put.getParam(1).getType().asTypeParameter().declaredOnType());
        assertEquals("java.util.Map.V", put.getParam(1).getType().asTypeParameter().getQualifiedName());
    }
}
