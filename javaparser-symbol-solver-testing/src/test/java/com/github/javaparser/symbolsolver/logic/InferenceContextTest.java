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

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * @author Federico Tomassetti
 */
class InferenceContextTest {

    private TypeSolver typeSolver;
    private ResolvedReferenceType string;
    private ResolvedReferenceType object;
    private ResolvedReferenceType listOfString;
    private ResolvedReferenceType listOfE;
    private ResolvedTypeParameterDeclaration tpE;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        listOfString = listOf(string);
        tpE = mock(ResolvedTypeParameterDeclaration.class);
        when(tpE.getName()).thenReturn("T");

        listOfE = listOf(new ResolvedTypeVariable(tpE));
    }

    private ResolvedReferenceType listOf(ResolvedType elementType) {
        return new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeSolver), ImmutableList.of(elementType), typeSolver);
    }

    @Test
    void noVariablesArePlacedWhenNotNeeded() {
        ResolvedType result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(object, string);
        assertEquals(object, result);
    }

    @Test
    void placingASingleVariableTopLevel() {
        ResolvedType result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(new ResolvedTypeVariable(tpE), listOfString);
        assertEquals(new InferenceVariableType(0, MyObjectProvider.INSTANCE), result);
    }

    @Test
    void placingASingleVariableInside() {
        ResolvedType result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(listOfE, listOfString);
        assertEquals(listOf(new InferenceVariableType(0, MyObjectProvider.INSTANCE)), result);
    }

}
