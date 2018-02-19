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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import org.junit.Test;

import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class FindingAllFields extends AbstractResolutionTest {

    @Test
    public void findAllInheritedFields() {
        CompilationUnit cu = parseSample("AClassWithFields");
        ClassOrInterfaceDeclaration classC = Navigator.demandClass(cu, "C");
        ResolvedReferenceTypeDeclaration typeDeclaration = JavaParserFacade.get(new ReflectionTypeSolver()).getTypeDeclaration(classC);
        assertEquals(3, typeDeclaration.getAllFields().size());
        assertEquals(ImmutableSet.of("a", "b", "c"),
                typeDeclaration.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
    }

    @Test
    public void findAllInheritedFieldsAndGenerics() {
        CompilationUnit cu = parseSample("AClassWithFieldsAndGenerics");
        ClassOrInterfaceDeclaration classC = Navigator.demandClass(cu, "C");
        ResolvedReferenceTypeDeclaration typeDeclaration = JavaParserFacade.get(new ReflectionTypeSolver()).getTypeDeclaration(classC);
        assertEquals(3, typeDeclaration.getAllFields().size());
        assertEquals(ImmutableSet.of("a", "b", "c"),
                typeDeclaration.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
        assertEquals("java.util.List<java.lang.String>", typeDeclaration.getField("b").getType().describe());
    }
}
