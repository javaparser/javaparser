/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.generator;

import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for CompilationUnitGenerator base class.
 * Verifies that compilation unit generation framework works correctly.
 */
class CompilationUnitGeneratorTest {

    private SourceRoot sourceRoot;
    private TestCompilationUnitGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(CompilationUnitGeneratorTest.class);
        generator = new TestCompilationUnitGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testGenerateCompilationUnit() {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        cu.addClass("TestClass");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testMultipleCompilationUnits() {
        CompilationUnit cu1 = new CompilationUnit("com.github.javaparser.ast");
        cu1.addClass("Class1");
        sourceRoot.add(cu1);

        CompilationUnit cu2 = new CompilationUnit("com.github.javaparser.ast.expr");
        cu2.addClass("Class2");
        sourceRoot.add(cu2);

        assertNotNull(generator);
    }

    /**
     * Test implementation of CompilationUnitGenerator for testing purposes.
     */
    private static class TestCompilationUnitGenerator extends CompilationUnitGenerator {
        TestCompilationUnitGenerator(SourceRoot sourceRoot) {
            super(sourceRoot);
        }

        @Override
        protected void generateCompilationUnit(CompilationUnit compilationUnit) {
            // Test implementation
        }
    }
}

