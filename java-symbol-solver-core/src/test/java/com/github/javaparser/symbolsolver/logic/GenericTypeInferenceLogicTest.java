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
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import javaslang.Tuple2;
import org.easymock.EasyMock;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

public class GenericTypeInferenceLogicTest {

    @Test
    public void inferGenericTypesTestEmptyCase() {
        assertEquals(Collections.emptyMap(), GenericTypeInferenceLogic.inferGenericTypes(Collections.emptyList()));
    }

    @Test
    public void inferGenericTypesTestSimpleCase() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        TypeParameterDeclaration a = EasyMock.createMock(TypeParameterDeclaration.class);
        EasyMock.expect(a.getName()).andReturn("A").anyTimes();
        EasyMock.replay(a);
        TypeVariable aUsage = new TypeVariable(a);
        assertEquals(ImmutableMap.of(a, string), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(aUsage, string))));
    }

    @Test
    public void inferGenericTypesTestSimpleCaseWithTwoSubstitutions() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        ReferenceType object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        TypeParameterDeclaration a = EasyMock.createMock(TypeParameterDeclaration.class);
        TypeParameterDeclaration b = EasyMock.createMock(TypeParameterDeclaration.class);
        TypeParameterDeclaration c = EasyMock.createMock(TypeParameterDeclaration.class);
        EasyMock.expect(a.getName()).andReturn("A").anyTimes();
        EasyMock.expect(b.getName()).andReturn("B").anyTimes();
        EasyMock.expect(c.getName()).andReturn("C").anyTimes();
        EasyMock.replay(a);
        EasyMock.replay(b);
        EasyMock.replay(c);
        TypeVariable aUsage = new TypeVariable(a);
        TypeVariable bUsage = new TypeVariable(b);
        TypeVariable cUsage = new TypeVariable(c);
        assertEquals(ImmutableMap.of(a, string, b, object, c, string), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(aUsage, string),
                        new Tuple2<Type, Type>(bUsage, object),
                        new Tuple2<Type, Type>(cUsage, string))));
    }

    @Test
    public void inferGenericTypesTestSimpleCaseNoSubstitutions() {
        TypeSolver typeSolver = new JreTypeSolver();
        ReferenceType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        ReferenceType object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        assertEquals(Collections.emptyMap(), GenericTypeInferenceLogic.inferGenericTypes(
                ImmutableList.of(new Tuple2<Type, Type>(object, string),
                        new Tuple2<Type, Type>(object, object),
                        new Tuple2<Type, Type>(object, string))));
    }
}
