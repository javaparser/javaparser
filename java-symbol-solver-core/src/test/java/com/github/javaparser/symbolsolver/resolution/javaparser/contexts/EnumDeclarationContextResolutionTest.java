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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.EnumDeclarationContext;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.DummyTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

/**
 * @author Federico Tomassetti
 */
public class EnumDeclarationContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
    }

    @Test
    public void solveSymbolReferringToDeclaredInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("i", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToDeclaredStaticField() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("j", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("long", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolReferringToValue() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        SymbolReference<? extends ValueDeclaration> ref = context.solveSymbol("E1", new DummyTypeSolver());
        assertEquals(true, ref.isSolved());
        assertEquals("MyEnum", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredInstanceField() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("i", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToDeclaredStaticField() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("j", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("long", ref.get().getType().describe());
    }

    @Test
    public void solveSymbolAsValueReferringToValue() throws ParseException {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("E1", new DummyTypeSolver());
        assertEquals(true, ref.isPresent());
        assertEquals("MyEnum", ref.get().getType().describe());
    }

}
