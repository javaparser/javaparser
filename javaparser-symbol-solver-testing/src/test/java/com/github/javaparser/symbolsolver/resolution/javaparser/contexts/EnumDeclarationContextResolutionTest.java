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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.EnumDeclarationContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Federico Tomassetti
 */
class EnumDeclarationContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    void solveSymbolReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("i");
        assertTrue(ref.isSolved());
        assertEquals("int", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("j");
        assertTrue(ref.isSolved());
        assertEquals("long", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolReferringToValue() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, new MemoryTypeSolver());

        SymbolReference<? extends ResolvedValueDeclaration> ref = context.solveSymbol("E1");
        assertTrue(ref.isSolved());
        assertEquals("MyEnum", ref.getCorrespondingDeclaration().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToDeclaredInstanceField() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("i");
        assertTrue(ref.isPresent());
        assertEquals("int", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToDeclaredStaticField() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("j");
        assertTrue(ref.isPresent());
        assertEquals("long", ref.get().getType().describe());
    }

    @Test
    void solveSymbolAsValueReferringToValue() {
        CompilationUnit cu = parseSample("AnEnum");
        com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "MyEnum");
        Context context = new EnumDeclarationContext(enumDeclaration, typeSolver);

        Optional<Value> ref = context.solveSymbolAsValue("E1");
        assertTrue(ref.isPresent());
        assertEquals("MyEnum", ref.get().getType().describe());
    }

}
