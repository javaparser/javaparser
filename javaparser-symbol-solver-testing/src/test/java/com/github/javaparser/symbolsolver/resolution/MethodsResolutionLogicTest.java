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

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

class MethodsResolutionLogicTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        Path srcNewCode = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode, new LeanParserConfiguration()));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"), new LeanParserConfiguration()));
        typeSolver = combinedTypeSolverNewCode;
    }

    @Test
    void compatibilityShouldConsiderAlsoTypeVariablesNegative() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedReferenceType stringType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(String.class, typeSolver);
        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
        assertEquals(true, rawClassType.isRawType());
        ResolvedReferenceType classOfStringType = (ResolvedReferenceType) rawClassType.replaceTypeVariables(rawClassType.getTypeDeclaration().get().getTypeParameters().get(0), stringType);
        MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

        assertEquals(false, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(classOfStringType), typeSolver));
    }

    @Test
    void compatibilityShouldConsiderAlsoTypeVariablesRaw() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
        MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

        assertEquals(true, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(rawClassType), typeSolver));
    }

    @Test
    void compatibilityShouldConsiderAlsoTypeVariablesPositive() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedReferenceType runtimeException = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(RuntimeException.class, typeSolver);
        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolver);
        ResolvedReferenceType classOfRuntimeType = (ResolvedReferenceType) rawClassType.replaceTypeVariables(rawClassType.getTypeDeclaration().get().getTypeParameters().get(0), runtimeException);
        MethodUsage mu = constructorDeclaration.getAllMethods().stream().filter(m -> m.getDeclaration().getSignature().equals("isThrows(java.lang.Class<? extends java.lang.Throwable>)")).findFirst().get();

        assertEquals(true, MethodResolutionLogic.isApplicable(mu, "isThrows", ImmutableList.of(classOfRuntimeType), typeSolver));
    }
}
