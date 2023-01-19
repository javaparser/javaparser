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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import org.junit.jupiter.api.Test;

import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

class FindingAllFieldsTest extends AbstractResolutionTest {

    @Test
    void findAllInheritedFields() {
        CompilationUnit cu = parseSample("AClassWithFields");
        ClassOrInterfaceDeclaration classC = Navigator.demandClass(cu, "C");
        ResolvedReferenceTypeDeclaration typeDeclaration = JavaParserFacade.get(new ReflectionTypeSolver()).getTypeDeclaration(classC);
        assertEquals(3, typeDeclaration.getAllFields().size());
        assertEquals(ImmutableSet.of("a", "b", "c"),
                typeDeclaration.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
    }

    @Test
    void findAllInheritedFieldsAndGenerics() {
        CompilationUnit cu = parseSample("AClassWithFieldsAndGenerics");
        ClassOrInterfaceDeclaration classC = Navigator.demandClass(cu, "C");
        ResolvedReferenceTypeDeclaration typeDeclaration = JavaParserFacade.get(new ReflectionTypeSolver()).getTypeDeclaration(classC);
        assertEquals(3, typeDeclaration.getAllFields().size());
        assertEquals(ImmutableSet.of("a", "b", "c"),
                typeDeclaration.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
        assertEquals("java.util.List<java.lang.String>", typeDeclaration.getField("b").getType().describe());
    }
}
