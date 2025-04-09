/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.StreamProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class ReflectionTypeSolverTest extends ClassLoaderTypeSolverTest<ReflectionTypeSolver> {

    public ReflectionTypeSolverTest() {
        super(ReflectionTypeSolver::new);
    }

    @Test
    void testHasType() {
        ReflectionTypeSolver ts = new ReflectionTypeSolver();
        assertEquals(true, ts.hasType(String.class.getCanonicalName()));
        assertEquals(true, ts.hasType(Object.class.getCanonicalName()));
        assertEquals(false, ts.hasType("foo.zum.unexisting"));
    }

    @Test()
    void testInvalidArgumentNumber() throws IOException {
        Path file = adaptPath("src/test/resources/issue2366/Test.java");

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());

        ParserConfiguration pc = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
                .setLanguageLevel(LanguageLevel.JAVA_8);

        JavaParser javaParser = new JavaParser(pc);

        CompilationUnit unit = javaParser
                .parse(
                        ParseStart.COMPILATION_UNIT,
                        new StreamProvider(Files.newInputStream(file), StandardCharsets.UTF_8.name()))
                .getResult()
                .get();

        Assertions.assertThrows(
                UnsolvedSymbolException.class,
                () -> unit.accept(
                        new VoidVisitorAdapter<Object>() {
                            @Override
                            public void visit(ObjectCreationExpr exp, Object arg) {
                                super.visit(exp, arg);
                                exp.resolve().getSignature();
                            }
                        },
                        null));
    }

    @Test
    void testFilteringAll() {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver(false);
        assertEquals(true, reflectionTypeSolver.hasType("java.lang.Object"));
        assertEquals(true, reflectionTypeSolver.hasType("org.xml.sax.Parser"));
        assertEquals(true, reflectionTypeSolver.hasType(this.getClass().getCanonicalName()));
    }

    @Test
    void testFilteringJRE() {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver(true);
        assertEquals(true, reflectionTypeSolver.hasType("java.lang.Object"));
        assertEquals(false, reflectionTypeSolver.hasType("org.xml.sax.Parser"));
        assertEquals(false, reflectionTypeSolver.hasType(this.getClass().getCanonicalName()));
    }

    @Test
    void testFilteringJCL() {
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver(ReflectionTypeSolver.JCL_ONLY);
        assertEquals(true, reflectionTypeSolver.hasType("java.lang.Object"));
        assertEquals(true, reflectionTypeSolver.hasType("org.xml.sax.Parser"));
        assertEquals(false, reflectionTypeSolver.hasType(this.getClass().getCanonicalName()));
    }
}
