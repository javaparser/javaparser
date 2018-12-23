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

import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

enum MyModifier {

}

public class ReflectionEnumDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver(false);



    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    public void testIsInterface() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    public void testIsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    public void testIsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    public void testAsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsClass() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        modifier.asClass();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        modifier.asInterface();
    }

    @Test
    public void testAsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    public void testGetPackageName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("com.github.javaparser.symbolsolver.reflectionmodel", modifier.getPackageName());
    }

    @Test
    public void testGetClassName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("MyModifier", modifier.getClassName());
    }

    @Test
    public void testGetQualifiedName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier", modifier.getQualifiedName());
    }

    @Test
    public void testInternalTypesEmpty() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(Collections.emptySet(), modifier.internalTypes());
    }

}
