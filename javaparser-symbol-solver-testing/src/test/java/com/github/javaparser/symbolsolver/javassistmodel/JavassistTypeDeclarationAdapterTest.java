/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.NotFoundException;
import org.junit.jupiter.api.extension.ExtensionContext;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.ArgumentsProvider;
import org.junit.jupiter.params.provider.ArgumentsSource;

import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.Arrays.asList;
import static java.util.Collections.singletonList;
import static org.junit.jupiter.api.Assertions.assertEquals;

class JavassistTypeDeclarationAdapterTest extends AbstractResolutionTest {

    @ParameterizedTest(name = "Given {0} is expected {1}")
    @ArgumentsSource(GetAncestorsProvider.class)
    void testGetAncestors(String ctClass, List<String> expectedAncestors) throws NotFoundException, IOException {
        TypeSolver typeSolver = new ReflectionTypeSolver(false);
        CtClass clazz = new ClassPool(true).getCtClass(ctClass);

        ResolvedReferenceTypeDeclaration declaration = JavassistFactory.toTypeDeclaration(clazz, typeSolver);
        JavassistTypeDeclarationAdapter adapter = new JavassistTypeDeclarationAdapter(clazz, typeSolver, declaration);

        List<ResolvedReferenceType> resultAncestors = adapter.getAncestors(false);
        assertEquals(expectedAncestors,
                resultAncestors.stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toList()));
    }

    /**
     * Class which provider arguments to be tested in {@link JavassistTypeDeclarationAdapterTest#testGetAncestors}
     */
    static class GetAncestorsProvider implements ArgumentsProvider {
        @Override
        public Stream<? extends Arguments> provideArguments(ExtensionContext extensionContext) {
            return Stream.of(
                    // Node
                    Arguments.of(
                            "com.github.javaparser.ast.Node",
                            asList(
                                    "java.lang.Object",
                                    "java.lang.Cloneable",
                                    "com.github.javaparser.HasParentNode",
                                    "com.github.javaparser.ast.visitor.Visitable",
                                    "com.github.javaparser.ast.nodeTypes.NodeWithRange",
                                    "com.github.javaparser.ast.nodeTypes.NodeWithTokenRange"
                            )
                    ),
                    // Expression
                    Arguments.of(
                            "com.github.javaparser.ast.expr.Expression",
                            singletonList(
                                    "com.github.javaparser.ast.Node"
                            )
                    ),
                    // Annotation.class
                    Arguments.of(
                            "com.github.javaparser.ParseStart",
                            singletonList(
                                    "java.lang.Object"
                            )
                    ),
                    // SlowTest Annotation
                    Arguments.of(
                            "com.github.javaparser.SlowTest",
                            asList(
                                    "java.lang.Object",
                                    "java.lang.annotation.Annotation"
                            )
                    )
            );
        }
    }

}
