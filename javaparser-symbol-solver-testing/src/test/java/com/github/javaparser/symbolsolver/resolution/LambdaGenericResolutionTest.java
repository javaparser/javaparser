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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class LambdaGenericResolutionTest extends AbstractSymbolResolutionTest {

    @Test
    void genericLambdas() {
        Path testFile= adaptPath("src/test/resources/GenericLambdas.java.txt");
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        JavaParser parser = new JavaParser(
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver))
        );
        CompilationUnit cu = null;
        try {
            cu = parser.parse(testFile).getResult().get();
        } catch (Exception e) {
            Assertions.fail(String.format("Failed to parse GenericLambdas.java due to %s", e.getMessage()), e);
        }

        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "GenericLambdas");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo");
        MethodCallExpr sinkCall = Navigator.demandNodeOfGivenClass(method, MethodCallExpr.class);

        Map<String, ResolvedType> types = sinkCall.getArguments().stream().collect(
                Collectors.toMap(Node::toString, Expression::calculateResolvedType)
        );

        assertEquals("java.lang.Float", types.get("i1").describe());
        assertEquals("java.lang.String", types.get("i2").describe());
    }

}
