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

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;
import com.github.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.easymock.EasyMock;
import org.junit.Before;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * @author Federico Tomassetti
 */
public class InferenceContextTest {

    private TypeSolver typeSolver;
    private ReferenceType string;
    private ReferenceType object;
    private ReferenceType listOfString;
    private ReferenceType listOfE;
    private TypeParameterDeclaration tpE;

    @Before
    public void setup() {
        typeSolver = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        listOfString = listOf(string);
        tpE = EasyMock.createMock(TypeParameterDeclaration.class);
        listOfE = listOf(new TypeVariable(tpE));
    }

    private ReferenceType listOf(Type elementType) {
        return new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeSolver), ImmutableList.of(elementType), typeSolver);
    }

    @Test
    public void noVariablesArePlacedWhenNotNeeded() {
        Type result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(object, string);
        assertEquals(object, result);
    }

    @Test
    public void placingASingleVariableTopLevel() {
        Type result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(new TypeVariable(tpE), listOfString);
        assertEquals(new InferenceVariableType(0, MyObjectProvider.INSTANCE), result);
    }

    @Test
    public void placingASingleVariableInside() {
        Type result = new InferenceContext(MyObjectProvider.INSTANCE).addPair(listOfE, listOfString);
        assertEquals(listOf(new InferenceVariableType(0, MyObjectProvider.INSTANCE)), result);
    }

}
