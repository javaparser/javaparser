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

import com.github.javaparser.symbolsolver.model.declarations.ClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.InterfaceDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

public class ReflectionMethodDeclarationTest {

    @Test
    public void testGetSignature() {
        TypeSolver typeResolver = new JreTypeSolver();

        ClassDeclaration object = new ReflectionClassDeclaration(Object.class, typeResolver);
        InterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);

        MethodDeclaration hashCode = object.getAllMethods().stream().filter(m -> m.getName().equals("hashCode")).findFirst().get().getDeclaration();
        MethodDeclaration equals = object.getAllMethods().stream().filter(m -> m.getName().equals("equals")).findFirst().get().getDeclaration();
        MethodDeclaration containsAll = list.getAllMethods().stream().filter(m -> m.getName().equals("containsAll")).findFirst().get().getDeclaration();
        MethodDeclaration subList = list.getAllMethods().stream().filter(m -> m.getName().equals("subList")).findFirst().get().getDeclaration();

        assertEquals("hashCode()", hashCode.getSignature());
        assertEquals("equals(java.lang.Object)", equals.getSignature());
        assertEquals("containsAll(java.util.Collection<? extends java.lang.Object>)", containsAll.getSignature());
        assertEquals("subList(int, int)", subList.getSignature());
    }
}
