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

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.logic.InferenceVariableType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
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
        string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver));
        object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver));
        listOfString = listOf(string);
        tpE = mock(ResolvedTypeParameterDeclaration.class);
        when(tpE.getName()).thenReturn("T");

        listOfE = listOf(new ResolvedTypeVariable(tpE));
    }

    private ResolvedReferenceType listOf(ResolvedType elementType) {
        return new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeSolver), ImmutableList.of(elementType));
    }

    @Test
    void noVariablesArePlacedWhenNotNeeded() {
        ResolvedType result = new InferenceContext(typeSolver).addPair(object, string);
        assertEquals(object, result);
    }

    @Test
    void placingASingleVariableTopLevel() {
        ResolvedType result = new InferenceContext(typeSolver).addPair(new ResolvedTypeVariable(tpE), listOfString);
        assertEquals(new InferenceVariableType(0, typeSolver), result);
    }

    @Test
    void placingASingleVariableInside() {
        ResolvedType result = new InferenceContext(typeSolver).addPair(listOfE, listOfString);
        assertEquals(listOf(new InferenceVariableType(0, typeSolver)), result);
    }

}
