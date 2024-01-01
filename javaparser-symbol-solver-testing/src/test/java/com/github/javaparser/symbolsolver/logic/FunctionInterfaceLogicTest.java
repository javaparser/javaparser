/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.function.Consumer;
import java.util.function.Function;

import org.junit.jupiter.api.Test;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class FunctionInterfaceLogicTest {

    @Test
    void testGetFunctionalMethodNegativeCaseOnClass() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver));
        assertEquals(false, FunctionalInterfaceLogic.getFunctionalMethod(string).isPresent());
    }

    @Test
    void testGetFunctionalMethodPositiveCasesOnInterfaces() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType function = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Function.class, typeSolver));
        assertEquals(true, FunctionalInterfaceLogic.getFunctionalMethod(function).isPresent());
        assertEquals("apply", FunctionalInterfaceLogic.getFunctionalMethod(function).get().getName());
        ResolvedType consumer = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Consumer.class, typeSolver));
        assertEquals(true, FunctionalInterfaceLogic.getFunctionalMethod(consumer).isPresent());
        assertEquals("accept", FunctionalInterfaceLogic.getFunctionalMethod(consumer).get().getName());
    }

    @Test
    void testGetFunctionalMethodWith2AbstractMethodsInHierarcy() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType function = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Foo.class, typeSolver));
        // By default, all methods in interface are public and abstract until we do not declare it
        // as default and properties are static and final.
        // This interface is not fonctional because it inherits two abstract methods
   	 	// which are not members of Object and the default apply method does not override the abstract apply method
        // defined in the Function interface.
        assertEquals(false, FunctionalInterfaceLogic.getFunctionalMethod(function).isPresent());
    }

    public static interface Foo<S, T> extends Function<S, T> {

        T foo(S str);

        @Override
		default T apply(S str) {
            return foo(str);
        }
    }
}
