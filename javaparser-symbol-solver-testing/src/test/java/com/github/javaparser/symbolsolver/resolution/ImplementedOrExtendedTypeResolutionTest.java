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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Tests resolution of implemented/extended types
 *
 * @author Takeshi D. Itoh
 */
class ImplementedOrExtendedTypeResolutionTest extends AbstractResolutionTest {

    @AfterEach
    void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        StaticJavaParser.getConfiguration().setSymbolResolver(null);
    }

    @Test
    void solveImplementedTypes() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ImplementedOrExtendedTypeResolution/ImplementedOrExtendedTypeResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "InterfaceTest");
        assertEquals(clazz.getFieldByName("field_i1").get().resolve().getType().describe(), "I1");
        assertEquals(clazz.getFieldByName("field_i2").get().resolve().getType().describe(), "I2.I2_1");
        assertEquals(clazz.getFieldByName("field_i3").get().resolve().getType().describe(), "I3.I3_1.I3_1_1");
    }

    @Test
    void solveExtendedType1() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ImplementedOrExtendedTypeResolution/ImplementedOrExtendedTypeResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassTest1");
        assertEquals(clazz.getFieldByName("field_c1").get().resolve().getType().describe(), "C1");
    }

    @Test
    void solveExtendedType2() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ImplementedOrExtendedTypeResolution/ImplementedOrExtendedTypeResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassTest2");
        assertEquals(clazz.getFieldByName("field_c2").get().resolve().getType().describe(), "C2.C2_1");
    }

    @Test
    void solveExtendedType3() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ImplementedOrExtendedTypeResolution/ImplementedOrExtendedTypeResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ClassTest3");
        assertEquals(clazz.getFieldByName("field_c3").get().resolve().getType().describe(), "C3.C3_1.C3_1_1");
    }

    @Test
    void solveImplementedTypeWithSameName() throws IOException {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(
            new JavaParserTypeSolver(adaptPath("src/test/resources/ImplementedOrExtendedTypeResolution/pkg"))));

        CompilationUnit cu = StaticJavaParser.parse(adaptPath("src/test/resources/ImplementedOrExtendedTypeResolution/pkg/main/A.java"));
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "A");
        String actual = clazz.getFieldByName("field_a").get().resolve().getType().describe();
        assertEquals("main.A", actual);
        assertNotEquals("another.A", actual);
    }

}
