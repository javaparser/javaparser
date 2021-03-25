/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.LazyType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserFacadeTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();

    private JavaParser parser;

    @BeforeEach
    void beforeEach() {
        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        parser = new JavaParser(configuration);
    }

    @Test
    void classToResolvedType_givenPrimitiveShouldBeAReflectionPrimitiveDeclaration() {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).classToResolvedType(int.class);
        assertEquals(int.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenClassShouldBeAReflectionClassDeclaration() {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).classToResolvedType(String.class);
        assertEquals(String.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenClassShouldBeAReflectionInterfaceDeclaration() {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).classToResolvedType(String.class);
        assertEquals(String.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenEnumShouldBeAReflectionEnumDeclaration() {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).classToResolvedType(TestEnum.class);
        assertEquals(TestEnum.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenAnnotationShouldBeAReflectionAnnotationDeclaration() {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).classToResolvedType(Override.class);
        assertEquals(Override.class.getCanonicalName(), resolvedType.describe());
    }

    /**
     * Enum to be tested in {@link JavaParserFacadeTest#classToResolvedType_givenEnumShouldBeAReflectionEnumDeclaration}.
     */
    private enum TestEnum {
        A, B;
    }

    @Test
    void convertToUsage_whenConvertingTypeWithTypeArgumentsTheArgumentsShouldBeLazy() {
        CompilationUnit cu = parser.parse("import java.util.List;\nclass A { List<String> list; }").getResult()
                .orElseThrow(AssertionError::new);
        Type listType = Navigator.demandNodeOfGivenClass(cu, Type.class);
        ResolvedReferenceType resolvedType = JavaParserFacade.get(typeSolver).convertToUsage(listType).asReferenceType();

        // Get the type parameter and check if it's lazy
        Optional<ResolvedType> typeParameter = resolvedType.getGenericParameterByName("E");
        assertTrue(typeParameter.isPresent());
        assertTrue(typeParameter.get() instanceof LazyType);

        // Check if the lazy type is initialized when needed.
        LazyType lazyType = (LazyType) typeParameter.get();
        assertEquals("java.util.List<java.lang.String>", resolvedType.describe());
        assertNotNull(lazyType.getType());
    }

}
