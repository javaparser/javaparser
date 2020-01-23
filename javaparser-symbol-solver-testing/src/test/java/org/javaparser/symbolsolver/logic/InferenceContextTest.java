/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.logic;

import org.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import org.javaparser.resolution.types.ResolvedReferenceType;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.resolution.types.ResolvedTypeVariable;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import org.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import org.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import org.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
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
