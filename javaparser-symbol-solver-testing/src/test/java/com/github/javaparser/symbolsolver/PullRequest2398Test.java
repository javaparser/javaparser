/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistClassDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;

/**
 * @author 谦扬
 * @date 2019-10-25
 */
public class PullRequest2398Test extends AbstractSymbolResolutionTest {
    private TypeSolver typeSolver;

    @Test
    void onlyInlucdeJarA() throws IOException {
        Path jarAPath = adaptPath("src/test/resources/pullRequest2398/A.jar");
        typeSolver = new CombinedTypeSolver(
            new JarTypeSolver(jarAPath),
            new ReflectionTypeSolver()
        );

        JavassistClassDeclaration classDecl = (JavassistClassDeclaration)typeSolver.solveType("A");
        JavassistMethodDeclaration method = findMethodWithName(classDecl, "b");
        try {
            method.getReturnType();
            throw new RuntimeException("should throw UnsolvedSymbolException");
        } catch (Exception e) {
            assert e instanceof UnsolvedSymbolException;
        }
    }

    @Test
    void includeJarAAndB() throws IOException {
        Path jarAPath = adaptPath("src/test/resources/pullRequest2398/A.jar");
        Path jarBPath = adaptPath("src/test/resources/pullRequest2398/B.jar");
        typeSolver = new CombinedTypeSolver(
            new JarTypeSolver(jarAPath),
            new JarTypeSolver(jarBPath),
            new ReflectionTypeSolver()
        );

        JavassistClassDeclaration classDecl = (JavassistClassDeclaration)typeSolver.solveType("A");
        JavassistMethodDeclaration method = findMethodWithName(classDecl, "b");
        final ResolvedType returnType = method.getReturnType();
        assertThat(returnType.describe(), is("B"));
    }

    private JavassistMethodDeclaration findMethodWithName(JavassistClassDeclaration classDecl, String name) {
        return classDecl.getDeclaredMethods().stream().filter(methodDecl -> methodDecl.getName().equals(name))
            .map(m -> (JavassistMethodDeclaration)m).findAny().get();
    }
}
