/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.time.Duration;
import java.util.List;
import java.util.Locale;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * @author Malte Langkabel
 */
class MethodContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    void solveTypeRefToLocalClass() {
        CompilationUnit cu = parseSample("MethodWithTypes");
        ClassOrInterfaceDeclaration cd = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(cd, "methodWithLocalTypes");
        Context context = new MethodContext(md, new MemoryTypeSolver());

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("LocalClass");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToLocalClassFindsTheSameDeclarationEveryTime() {
        MethodDeclaration md = methodWithLocalTypes();
        ClassOrInterfaceDeclaration localClass =
                md.findFirst(ClassOrInterfaceDeclaration.class).get();
        for (int lookup = 0; lookup < 2; lookup++) {
            SymbolReference<ResolvedTypeDeclaration> ref = new MethodContext(md, typeSolver).solveType("LocalClass");
            assertSame(localClass, ref.getCorrespondingDeclaration().toAst().get());
        }
    }

    /**
     * A clone carries the data of the node it was cloned from, including the local types found in it. The clone
     * must still resolve to its own local class, not to the original's.
     */
    @Test
    void solveTypeRefToLocalClassInAClonedMethod() {
        MethodDeclaration md = methodWithLocalTypes();
        new MethodContext(md, typeSolver).solveType("LocalClass");
        MethodDeclaration clone = md.clone();
        ClassOrInterfaceDeclaration clonedLocalClass =
                clone.findFirst(ClassOrInterfaceDeclaration.class).get();

        SymbolReference<ResolvedTypeDeclaration> ref = new MethodContext(clone, typeSolver).solveType("LocalClass");
        assertSame(clonedLocalClass, ref.getCorrespondingDeclaration().toAst().get());
    }

    /**
     * Every type name looked up inside a method is checked against the types declared in it. Those are found once
     * per method rather than by walking the whole method for every lookup, so resolving the types in a method grows
     * with its size, not with its size squared. Before, this method took about 30 seconds.
     */
    @Test
    void resolvingTypesInALargeMethodStaysFast() {
        StringBuilder source = new StringBuilder("class Big {\n    void method() {\n");
        for (int i = 0; i < 10_000; i++) {
            source.append(String.format(Locale.ROOT, "        String s%1$d = \"%1$d\";\n", i));
        }
        source.append("    }\n}\n");
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        List<VariableDeclarator> variables = new JavaParser(configuration)
                .parse(source.toString())
                .getResult()
                .get()
                .findAll(VariableDeclarator.class);

        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            for (VariableDeclarator variable : variables) {
                assertEquals("java.lang.String", variable.getType().resolve().describe());
            }
        });
    }

    private MethodDeclaration methodWithLocalTypes() {
        CompilationUnit cu = parseSample("MethodWithTypes");
        return Navigator.demandMethod(Navigator.demandClass(cu, "Main"), "methodWithLocalTypes");
    }
}
